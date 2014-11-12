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
import Data.Ratio((%))


-- | Results of checking for satisfiability.
data SmtRes = Unsat | Unknown | Sat
              deriving (Eq,Show)

-- | Common values returned by SMT solvers.
data SmtVal = SmtInt !Integer | SmtReal !Rational | SmtBool Bool
            | SmtOther SExpr
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


-- | Start a new solver process, using the given executable and arguments.
startSolverProcess :: String -> [String] -> IO SolverProcess
startSolverProcess exe opts =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     -- XXX: Ignore errors for now.
     _ <- forkIO $ forever (hGetLine hErr)
                    `X.catch` \X.SomeException {} -> return ()

     getResponse <-
       do txt <- hGetContents hOut                  -- Read *all* output
          ref <- newIORef (unfoldr parseSExpr txt)  -- Parse, and store result
          return $ atomicModifyIORef ref $ \xs ->
                      case xs of
                        []     -> (xs, Nothing)
                        y : ys -> (ys, Just y)

     let cmd c = do hPutStrLn hIn $ renderSExpr c ""
                    hFlush hIn

         solverDo c =
           do cmd c
              mb <- getResponse
              case mb of
                Just res -> return res
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
    SAtom txt
      | Just n <- readMaybe txt     -> SmtInt n
    SList [ SAtom "-", x ]
      | SmtInt a <- sexprToVal x    -> SmtInt (negate a)
    SList [ SAtom "/", x, y ]
      | SmtInt a <- sexprToVal x
      , SmtInt b <- sexprToVal y    -> SmtReal (a % b)
    _ -> SmtOther expr


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








