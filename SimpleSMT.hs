{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
module SimpleSMT where

import Data.Char(isSpace)
import Data.List(unfoldr)
import Data.IORef(newIORef, atomicModifyIORef, modifyIORef', readIORef)
import System.Process(runInteractiveProcess, waitForProcess)
import System.IO (hFlush, hGetLine, hGetContents, hPutStrLn, stdout)
import System.Exit(ExitCode)
import qualified Control.Exception as X
import Control.Concurrent(forkIO)
import Control.Monad(forever)
import Text.Read(readMaybe)
import Data.Ratio((%), numerator, denominator)
import Numeric(readHex)


-- | Results of checking for satisfiability.
data SmtRes = Unsat | Unknown | Sat
              deriving (Eq,Show)

-- | Common values returned by SMT solvers.
data SmtVal = SmtInt !Integer
            | SmtReal !Rational
            | SmtBool !Bool
            | SmtBits !Int !Integer   -- ^ width, value
            | SmtOther !SExpr
              deriving (Eq,Show)

-- | S-expressions, which are used in SMTLIB-2.
data SExpr  = SAtom String | SList [SExpr]
              deriving (Eq, Show)

-- | Show an s-expression.
renderSExpr :: SExpr -> ShowS
renderSExpr ex =
  case ex of
    SAtom x  -> showString x
    SList es -> showChar '(' .
                foldr (\e m -> renderSExpr e . showChar ' ' . m)
                (showChar ')') es

-- | Parse an s-expression.
parseSExpr :: String -> Maybe (SExpr, String)
parseSExpr (c : more) | isSpace c = parseSExpr more
parseSExpr ('(' : more) = do (xs,more1) <- list more
                             return (SList xs, more1)
  where
  list (c : txt) | isSpace c = list txt
  list (')' : txt) = return ([], txt)
  list txt         = do (v,txt1) <- parseSExpr txt
                        (vs,txt2) <- list txt1
                        return (v:vs, txt2)
parseSExpr txt     = case break end txt of
                       (as,bs) | not (null as) -> Just (SAtom as, bs)
                       _ -> Nothing
  where end x = x == ')' || isSpace x


--------------------------------------------------------------------------------

-- | Inetract with a solver process.
data SolverProcess = SolverProcess
  { solverDo   :: SExpr -> IO SExpr
    -- ^ Send a command from the solver.

  , solverStop :: IO ExitCode
    -- ^ Terminate the solver.
  }


-- | Start a new solver process.
startSolverProcess :: String       {- ^ Executable -}      ->
                      [String]     {- ^ Argumetns -}       ->
                      Maybe Logger {- ^ Be verbose here -} ->
                      IO SolverProcess
startSolverProcess exe opts mbLog =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     let info a = case mbLog of
                    Nothing -> return ()
                    Just l  -> logMessage l a

     -- XXX: Ignore errors for now.
     _ <- forkIO $ forever $ do errs <- hGetLine hErr
                                info ("[stderr] " ++ errs)
                    `X.catch` \X.SomeException {} -> return ()

     getResponse <-
       do txt <- hGetContents hOut                  -- Read *all* output
          ref <- newIORef (unfoldr parseSExpr txt)  -- Parse, and store result
          return $ atomicModifyIORef ref $ \xs ->
                      case xs of
                        []     -> (xs, Nothing)
                        y : ys -> (ys, Just y)

     let cmd c = do let txt = renderSExpr c ""
                    info ("[send->] " ++ txt)
                    hPutStrLn hIn txt
                    hFlush hIn

         solverDo c =
           do cmd c
              mb <- getResponse
              case mb of
                Just res -> do info ("[<-recv] " ++ renderSExpr res "")
                               return res
                Nothing  -> fail "Missing response from solver"

         solverStop =
           do cmd (SList [SAtom "exit"])
              waitForProcess h

         solver = SolverProcess { .. }

     solverSimpleCmd solver [ "set-option", ":print-success", "true" ]
     solverSimpleCmd solver [ "set-option", ":produce-models", "true" ]

     return solver



-- | A command with no interesting result.
solverAckCmd :: SolverProcess -> SExpr -> IO ()
solverAckCmd proc c =
  do res <- solverDo proc c
     case res of
       SAtom "success" -> return ()
       _  -> fail $ unlines
                      [ "Unexpected result from the SMT solver:"
                      , "  Expected: success"
                      , "  Result: " ++ renderSExpr res ""
                      ]

-- | A command entirely made out of atoms, with no interesting result.
solverSimpleCmd :: SolverProcess -> [String] -> IO ()
solverSimpleCmd proc = solverAckCmd proc . SList . map SAtom


-- | Checkpoint state
solverPush :: SolverProcess -> IO ()
solverPush proc = solverSimpleCmd proc [ "push", "1" ]

-- | Restore to last check-point
solverPop :: SolverProcess -> IO ()
solverPop proc = solverSimpleCmd proc [ "pop", "1" ]

solverDeclareFun :: SolverProcess -> String -> [SExpr] -> SExpr -> IO ()
solverDeclareFun proc f as r =
  solverAckCmd proc $ smtFun "declare-fun" [ SAtom f, SList as, r ]

-- | Assume a fact
solverAssume :: SolverProcess -> SExpr -> IO ()
solverAssume proc e = solverAckCmd proc $ SList [ SAtom "assert", e ]

-- | Check if assumptions are consistent. Does not return a model.
solverCheck :: SolverProcess -> IO SmtRes
solverCheck proc =
  do res <- solverDo proc (SList [ SAtom "check-sat" ])
     case res of
       SAtom "unsat"   -> return Unsat
       SAtom "unknown" -> return Unknown
       SAtom "sat"     -> return Sat
       _ -> fail $ unlines
              [ "Unexpected result from the SMT solver:"
              , "  Expected: unsat, unknown, or sat"
              , "  Result: " ++ renderSExpr res ""
              ]

-- | Convert an s-expression to a value.
sexprToVal :: SExpr -> SmtVal
sexprToVal expr =
  case expr of
    SAtom "true"                    -> SmtBool True
    SAtom "false"                   -> SmtBool False
    SAtom ('#' : 'b' : ds)
      | Just n <- binLit ds         -> SmtBits (length ds) n
    SAtom ('#' : 'x' : ds)
      | [(n,[])] <- readHex ds      -> SmtBits (4 * length ds) n
    SAtom txt
      | Just n <- readMaybe txt     -> SmtInt n
    SList [ SAtom "-", x ]
      | SmtInt a <- sexprToVal x    -> SmtInt (negate a)
    SList [ SAtom "/", x, y ]
      | SmtInt a <- sexprToVal x
      , SmtInt b <- sexprToVal y    -> SmtReal (a % b)
    _ -> SmtOther expr

  where
  binLit cs = do ds <- mapM binDigit cs
                 return $ sum $ zipWith (*) (reverse ds) powers2
  powers2   = 1 : map (2 *) powers2
  binDigit '0' = Just 0
  binDigit '1' = Just 1
  binDigit _   = Nothing

-- | Get the values of some s-expressions.
-- Only valid after a 'Sat' result.
solverGetExprs :: SolverProcess -> [SExpr] -> IO [SmtVal]
solverGetExprs proc vals =
  do res <- solverDo proc $ SList [ SAtom "get-value", SList vals ]
     case res of
       SList xs -> return (map sexprToVal xs)
       _ -> fail $ unlines
                 [ "Unexpected response from the SMT solver:"
                 , "  Exptected: a list"
                 , "  Result: " ++ renderSExpr res ""
                 ]

-- | Get the values of some variables in the current model.
-- Only valid after a 'Sat' result.
solverGetVars :: SolverProcess -> [String] -> IO [SmtVal]
solverGetVars proc xs = solverGetExprs proc (map SAtom xs)


--------------------------------------------------------------------------------


smtFam :: String -> [Integer] -> SExpr
smtFam f is = SList (SAtom "_" : SAtom f : map (SAtom . show) is)

smtFun :: String -> [SExpr] -> SExpr
smtFun f [] = SAtom f
smtFun f as = SList (SAtom f : as)

smtConst :: String -> SExpr
smtConst f = smtFun f []


stmIntT :: SExpr
stmIntT = smtConst "Int"

stmBoolT :: SExpr
stmBoolT = smtConst "Bool"

smtRealT :: SExpr
smtRealT = smtConst "Real"

smtArrayT :: SExpr -> SExpr -> SExpr
smtArrayT x y = smtFun "Array" [x,y]

smtBitsT :: Integer -> SExpr
smtBitsT w = smtFam "BitVec" [w]


smtTrue :: SExpr
smtTrue = smtConst "true"

smtFalse :: SExpr
smtFalse = smtConst "false"

smtNot :: SExpr -> SExpr
smtNot p = smtFun "not" [p]

smtAnd :: SExpr -> SExpr -> SExpr
smtAnd p q = smtFun "and" [p,q]

smtOr :: SExpr -> SExpr -> SExpr
smtOr p q = smtFun "or" [p,q]

smtXor :: SExpr -> SExpr -> SExpr
smtXor p q = smtFun "xor" [p,q]

smtImplies :: SExpr -> SExpr -> SExpr
smtImplies p q = smtFun "=>" [p,q]



smtITE :: SExpr -> SExpr -> SExpr -> SExpr
smtITE x y z = smtFun "ite" [x,y,z]

smtEq :: SExpr -> SExpr -> SExpr
smtEq x y = smtFun "=" [x,y]


smtInt :: Integer -> SExpr
smtInt x | x < 0     = smtNeg (smtInt (negate x))
         | otherwise = SAtom (show x)

smtReal :: Rational -> SExpr
smtReal x = smtRealDiv (smtInt (denominator x)) (smtInt (numerator x))

smtGt :: SExpr -> SExpr -> SExpr
smtGt x y = smtFun ">" [x,y]

smtLt :: SExpr -> SExpr -> SExpr
smtLt x y = smtFun "<" [x,y]

smtGeq :: SExpr -> SExpr -> SExpr
smtGeq x y = smtFun "<=" [x,y]

smtLeq :: SExpr -> SExpr -> SExpr
smtLeq x y = smtFun "<=" [x,y]



smtAdd :: SExpr -> SExpr -> SExpr
smtAdd x y = smtFun "+" [x,y]

smtSub :: SExpr -> SExpr -> SExpr
smtSub x y = smtFun "-" [x,y]

smtNeg :: SExpr -> SExpr
smtNeg x = smtFun "-" [x]

smtMul :: SExpr -> SExpr -> SExpr
smtMul x y = smtFun "*" [x,y]

smtAbs :: SExpr -> SExpr
smtAbs x = smtFun "abs" [x]

smtDiv :: SExpr -> SExpr -> SExpr
smtDiv x y = smtFun "div" [x,y]

smtMod :: SExpr -> SExpr -> SExpr
smtMod x y = smtFun "mod" [x,y]

smtDivisible :: SExpr -> Integer -> SExpr
smtDivisible x n = SList [ smtFam "divisible" [n], x ]

smtRealDiv :: SExpr -> SExpr -> SExpr
smtRealDiv x y = smtFun "/" [x,y]


smtConcat :: SExpr -> SExpr -> SExpr
smtConcat x y = smtFun "concat" [x,y]

smtExtract :: SExpr -> Integer -> Integer -> SExpr
smtExtract x y z = SList [ smtFam "extract" [y,z], x ]

smtBvNot :: SExpr -> SExpr
smtBvNot x = smtFun "bvnot" [x]

smtBvNeg :: SExpr -> SExpr
smtBvNeg x = smtFun "bvneg" [x]

smtBvAnd :: SExpr -> SExpr -> SExpr
smtBvAnd x y = smtFun "bvand" [x,y]

smtBvOr :: SExpr -> SExpr -> SExpr
smtBvOr x y = smtFun "bvor" [x,y]

smtBvAdd :: SExpr -> SExpr -> SExpr
smtBvAdd x y = smtFun "bvadd" [x,y]

smtBvMul :: SExpr -> SExpr -> SExpr
smtBvMul x y = smtFun "bvmul" [x,y]

smtBvUDiv :: SExpr -> SExpr -> SExpr
smtBvUDiv x y = smtFun "bvudiv" [x,y]

smtBvURem :: SExpr -> SExpr -> SExpr
smtBvURem x y = smtFun "bvurem" [x,y]

smtBvShl :: SExpr -> SExpr -> SExpr
smtBvShl x y = smtFun "bvshl" [x,y]

smtBvLShr :: SExpr -> SExpr -> SExpr
smtBvLShr x y = smtFun "bvshr" [x,y]

smtBvULt :: SExpr -> SExpr -> SExpr
smtBvULt x y = smtFun "bvult" [x,y]

smtSelect :: SExpr -> SExpr -> SExpr
smtSelect x y = smtFun "select" [x,y]

smtStore :: SExpr -> SExpr -> SExpr -> SExpr
smtStore x y z = smtFun "store" [x,y,z]



--------------------------------------------------------------------------------

-- | Log messages with minimal formatting. Mostly for debugging.
data Logger = Logger
  { logMessage :: String -> IO ()
    -- ^ Log a message.

  , logTab     :: IO ()
    -- ^ Increase indentation.

  , logUntab   :: IO ()
    -- ^ Decrease indentation.
  }

-- | A simple stdout logger.
newLogger :: IO Logger
newLogger =
  do tab <- newIORef 0
     let logMessage x = do let ls = lines x
                           t <- readIORef tab
                           putStr $ unlines [ replicate t ' ' ++ l | l <- ls ]
                           hFlush stdout
         logTab   = modifyIORef' tab (+ 4)
         logUntab = modifyIORef' tab (subtract 4)
     return Logger { .. }








