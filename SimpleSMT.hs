{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
-- | A module for interacting with an SMT solver, using SmtLib-2 format.
module SimpleSMT
  (
    -- * Basic Solver Interface
    Solver
  , newSolver
  , command
  , stop
  , ackCommand
  , simpleCommand

    -- ** S-Expressions
  , SExpr(..)
  , showsSExpr, readSExpr

    -- ** Logging and Debugging
  , Logger(..)
  , newLogger

    -- * Common SmtLib-2 Commands
  , setLogic
  , push, pushMany
  , pop, popMany
  , declare
  , declareFun
  , assert
  , check
  , Result(..)
  , getExprs
  , getVars
  , Value(..)

    -- * Convenienct Functoins for SmtLib-2 Epxressions
  , smtFam
  , smtFun
  , smtConst

    -- ** Types
  , tInt
  , tBool
  , tReal
  , tArray
  , tBits

    -- ** Literals
  , int
  , real
  , bool
  , bvBin
  , bvHex

    -- ** Connectives
  , not
  , and
  , or
  , xor
  , implies

    -- ** If-then-else
  , ite

    -- ** Relational Predicates
  , eq
  , gt
  , lt
  , geq
  , leq
  , bvULt

    -- ** Arithmetic
  , add
  , sub
  , neg
  , mul
  , abs
  , div
  , mod
  , divisible
  , realDiv

    -- ** Bit Vectors
  , concat
  , extract
  , bvNot
  , bvNeg
  , bvAnd
  , bvOr
  , bvAdd
  , bvMul
  , bvUDiv
  , bvURem
  , bvShl
  , bvLShr

    -- ** Arrays
  , select
  , store
  ) where

import Prelude hiding (not, and, or, abs, div, mod, concat)
import qualified Prelude as P
import Data.Char(isSpace)
import Data.List(unfoldr)
import Data.Bits(testBit)
import Data.IORef(newIORef, atomicModifyIORef, modifyIORef', readIORef)
import System.Process(runInteractiveProcess, waitForProcess)
import System.IO (hFlush, hGetLine, hGetContents, hPutStrLn, stdout)
import System.Exit(ExitCode)
import qualified Control.Exception as X
import Control.Concurrent(forkIO)
import Control.Monad(forever)
import Text.Read(readMaybe)
import Data.Ratio((%), numerator, denominator)
import Numeric(showHex, readHex)


-- | Results of checking for satisfiability.
data Result = Sat         -- ^ The assertions are satisfiable
            | Unsat       -- ^ The assertions are unsatisfiable
            | Unknown     -- ^ The result is inconclusive
              deriving (Eq,Show)

-- | Common values returned by SMT solvers.
data Value =  Bool  !Bool           -- ^ Boolean value
            | Int   !Integer        -- ^ Integral value
            | Real  !Rational       -- ^ Rational value
            | Bits  !Int !Integer   -- ^ Bit vector: width, value
            | Other !SExpr          -- ^ Some other value
              deriving (Eq,Show)

-- | S-expressions. These are the basic format for SmtLib-2.
data SExpr  = Atom String
            | List [SExpr]
              deriving (Eq, Show)

-- | Show an s-expression.
showsSExpr :: SExpr -> ShowS
showsSExpr ex =
  case ex of
    Atom x  -> showString x
    List es -> showChar '(' .
                foldr (\e m -> showsSExpr e . showChar ' ' . m)
                (showChar ')') es

-- | Parse an s-expression.
readSExpr :: String -> Maybe (SExpr, String)
readSExpr (c : more) | isSpace c = readSExpr more
readSExpr ('(' : more) = do (xs,more1) <- list more
                            return (List xs, more1)
  where
  list (c : txt) | isSpace c = list txt
  list (')' : txt) = return ([], txt)
  list txt         = do (v,txt1) <- readSExpr txt
                        (vs,txt2) <- list txt1
                        return (v:vs, txt2)
readSExpr txt     = case break end txt of
                       (as,bs) | P.not (null as) -> Just (Atom as, bs)
                       _ -> Nothing
  where end x = x == ')' || isSpace x


--------------------------------------------------------------------------------

-- | An interactive solver process.
data Solver = Solver
  { command   :: SExpr -> IO SExpr
    -- ^ Send a command to the solver.

  , stop :: IO ExitCode
    -- ^ Terminate the solver.
  }


-- | Start a new solver process.
newSolver :: String       {- ^ Executable -}             ->
             [String]     {- ^ Argumetns -}              ->
             Maybe Logger {- ^ Optional logging herer -} ->
             IO Solver
newSolver exe opts mbLog =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     let info a = case mbLog of
                    Nothing -> return ()
                    Just l  -> logMessage l a

     _ <- forkIO $ forever $ do errs <- hGetLine hErr
                                info ("[stderr] " ++ errs)
                    `X.catch` \X.SomeException {} -> return ()

     getResponse <-
       do txt <- hGetContents hOut                  -- Read *all* output
          ref <- newIORef (unfoldr readSExpr txt)  -- Parse, and store result
          return $ atomicModifyIORef ref $ \xs ->
                      case xs of
                        []     -> (xs, Nothing)
                        y : ys -> (ys, Just y)

     let cmd c = do let txt = showsSExpr c ""
                    info ("[send->] " ++ txt)
                    hPutStrLn hIn txt
                    hFlush hIn

         command c =
           do cmd c
              mb <- getResponse
              case mb of
                Just res -> do info ("[<-recv] " ++ showsSExpr res "")
                               return res
                Nothing  -> fail "Missing response from solver"

         stop =
           do cmd (List [Atom "exit"])
              waitForProcess h

         solver = Solver { .. }

     setOption solver ":print-success" "true"
     setOption solver ":produce-models" "true"

     return solver



-- | A command with no interesting result.
ackCommand :: Solver -> SExpr -> IO ()
ackCommand proc c =
  do res <- command proc c
     case res of
       Atom "success" -> return ()
       _  -> fail $ unlines
                      [ "Unexpected result from the SMT solver:"
                      , "  Expected: success"
                      , "  Result: " ++ showsSExpr res ""
                      ]

-- | A command entirely made out of atoms, with no interesting result.
simpleCommand :: Solver -> [String] -> IO ()
simpleCommand proc = ackCommand proc . List . map Atom


-- | Set a solver option.
setOption :: Solver -> String -> String -> IO ()
setOption s x y = simpleCommand s [ "set-option", x, y ]

-- | Set the solver's logic.  Usually, this should be done first.
setLogic :: Solver -> String -> IO ()
setLogic s x = simpleCommand s [ "set-logic", x ]


-- | Checkpoint state.  A special case of 'pushMany'.
push :: Solver -> IO ()
push proc = pushMany proc 1

-- | Restore to last check-point.  A sepcial case of 'popMany'.
pop :: Solver -> IO ()
pop proc = popMany proc 1

-- | Push multiple scopes.
pushMany :: Solver -> Integer -> IO ()
pushMany proc n = simpleCommand proc [ "push", show n ]

-- | Pop multiple scopes.
popMany :: Solver -> Integer -> IO ()
popMany proc n = simpleCommand proc [ "push", show n ]



-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns an the declared name as a constant expression.
declare :: Solver -> String -> SExpr -> IO SExpr
declare proc f t = declareFun proc f [] t

-- | Declare a function or a constant.
-- For convenience, returns an the declared name as a constant expression.
declareFun :: Solver -> String -> [SExpr] -> SExpr -> IO SExpr
declareFun proc f as r =
  do ackCommand proc $ smtFun "declare-fun" [ Atom f, List as, r ]
     return (smtConst f)

-- | Assume a fact.
assert :: Solver -> SExpr -> IO ()
assert proc e = ackCommand proc $ smtFun "assert" [e]

-- | Check if the current set of assertion is consistent.
check :: Solver -> IO Result
check proc =
  do res <- command proc $ smtConst "check-sat"
     case res of
       Atom "unsat"   -> return Unsat
       Atom "unknown" -> return Unknown
       Atom "sat"     -> return Sat
       _ -> fail $ unlines
              [ "Unexpected result from the SMT solver:"
              , "  Expected: unsat, unknown, or sat"
              , "  Result: " ++ showsSExpr res ""
              ]

-- | Convert an s-expression to a value.
sexprToVal :: SExpr -> Value
sexprToVal expr =
  case expr of
    Atom "true"                    -> Bool True
    Atom "false"                   -> Bool False
    Atom ('#' : 'b' : ds)
      | Just n <- binLit ds         -> Bits (length ds) n
    Atom ('#' : 'x' : ds)
      | [(n,[])] <- readHex ds      -> Bits (4 * length ds) n
    Atom txt
      | Just n <- readMaybe txt     -> Int n
    List [ Atom "-", x ]
      | Int a <- sexprToVal x    -> Int (negate a)
    List [ Atom "/", x, y ]
      | Int a <- sexprToVal x
      , Int b <- sexprToVal y    -> Real (a % b)
    _ -> Other expr

  where
  binLit cs = do ds <- mapM binDigit cs
                 return $ sum $ zipWith (*) (reverse ds) powers2
  powers2   = 1 : map (2 *) powers2
  binDigit '0' = Just 0
  binDigit '1' = Just 1
  binDigit _   = Nothing

-- | Get the values of some s-expressions.
-- Only valid after a 'Sat' result.
getExprs :: Solver -> [SExpr] -> IO [Value]
getExprs proc vals =
  do res <- command proc $ List [ Atom "get-value", List vals ]
     case res of
       List xs -> return (map sexprToVal xs)
       _ -> fail $ unlines
                 [ "Unexpected response from the SMT solver:"
                 , "  Exptected: a list"
                 , "  Result: " ++ showsSExpr res ""
                 ]

-- | Get the values of some variables in the current model.
-- A special case of 'getExprs'.
-- Only valid after a 'Sat' result.
getVars :: Solver -> [String] -> IO [Value]
getVars proc xs = getExprs proc (map Atom xs)


--------------------------------------------------------------------------------


-- | A constant, corresponding to a family indexed by some integers.
smtFam :: String -> [Integer] -> SExpr
smtFam f is = List (Atom "_" : Atom f : map (Atom . show) is)

-- | An SMT function.
smtFun :: String -> [SExpr] -> SExpr
smtFun f [] = Atom f
smtFun f as = List (Atom f : as)

-- | An SMT constant.  A special case of 'smtFun'.
smtConst :: String -> SExpr
smtConst f = smtFun f []


-- Types -----------------------------------------------------------------------


-- | The type of integers.
tInt :: SExpr
tInt = smtConst "Int"

-- | The type of booleans.
tBool :: SExpr
tBool = smtConst "Bool"

-- | The type of reals.
tReal :: SExpr
tReal = smtConst "Real"

-- | The type of arrays.
tArray :: SExpr {- ^ Type of indexes  -} ->
          SExpr {- ^ Type of elements -} ->
          SExpr
tArray x y = smtFun "Array" [x,y]

-- | The type of bit vectors.
tBits :: Integer {- ^ Number of bits -} ->
         SExpr
tBits w = smtFam "BitVec" [w]



-- Literals --------------------------------------------------------------------

-- | Boolean literals.
bool :: Bool -> SExpr
bool b = smtConst (if b then "true" else "false")

-- | Integer literals.
int :: Integer -> SExpr
int x | x < 0     = neg (int (negate x))
         | otherwise = Atom (show x)

-- | Real (well, reational) literals.
real :: Rational -> SExpr
real x = realDiv (int (denominator x)) (int (numerator x))

-- | A bit vector represented in binary.
--
--     * If the value does not fit in the bits, then the bits will be increased.
--     * The width should be strictly positive.
bvBin :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvBin w v = smtConst ("#b" ++ bits)
  where
  bits = reverse [ if testBit v n then '1' else '0' | n <- [ 0 .. w - 1 ] ]

-- | A bit vector represented in hex.
--
--    * If the value does not fit in the bits, the bits will be increased to
--      the next multiple of 4 that will fit the value.
--    * If the width is not a multiple of 4, it will be rounded
--      up so that it is.
--    * The width should be strictly positive.
bvHex :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvHex w v = smtConst ("#x" ++ padding ++ hex)
  where
  hex     = showHex v ""
  padding = replicate (P.div (w + 3) 4 - length hex) '0'



-- Connectives -----------------------------------------------------------------

-- | Logical negation.
not :: SExpr -> SExpr
not p = smtFun "not" [p]

-- | Conjucntion.
and :: SExpr -> SExpr -> SExpr
and p q = smtFun "and" [p,q]

-- | Disjunction.
or :: SExpr -> SExpr -> SExpr
or p q = smtFun "or" [p,q]

-- | Exclusive-or.
xor :: SExpr -> SExpr -> SExpr
xor p q = smtFun "xor" [p,q]

-- | Implication.
implies :: SExpr -> SExpr -> SExpr
implies p q = smtFun "=>" [p,q]


-- If-then-else ----------------------------------------------------------------

-- | If-then-else.  This is polymorphic and can be used to construct any term.
ite :: SExpr -> SExpr -> SExpr -> SExpr
ite x y z = smtFun "ite" [x,y,z]




-- Relations -------------------------------------------------------------------

-- | Equality.
eq :: SExpr -> SExpr -> SExpr
eq x y = smtFun "=" [x,y]

-- | Greather-then
gt :: SExpr -> SExpr -> SExpr
gt x y = smtFun ">" [x,y]

-- | Less-then.
lt :: SExpr -> SExpr -> SExpr
lt x y = smtFun "<" [x,y]

-- | Greater-than-or-equal-to.
geq :: SExpr -> SExpr -> SExpr
geq x y = smtFun "<=" [x,y]

-- | Less-than-or-equal-to.
leq :: SExpr -> SExpr -> SExpr
leq x y = smtFun "<=" [x,y]

-- | Unsigned less-than on bit-vectors.
bvULt :: SExpr -> SExpr -> SExpr
bvULt x y = smtFun "bvult" [x,y]




-- | Addition.
-- See also 'bvAdd'
add :: SExpr -> SExpr -> SExpr
add x y = smtFun "+" [x,y]

-- | Subtraction.
sub :: SExpr -> SExpr -> SExpr
sub x y = smtFun "-" [x,y]

-- | Arithmetic negation for integers and reals.
-- See also 'bvNeg'.
neg :: SExpr -> SExpr
neg x = smtFun "-" [x]

-- | Multiplication.
mul :: SExpr -> SExpr -> SExpr
mul x y = smtFun "*" [x,y]

-- | Absolute value.
abs :: SExpr -> SExpr
abs x = smtFun "abs" [x]

-- | Integer division.
div :: SExpr -> SExpr -> SExpr
div x y = smtFun "div" [x,y]

-- | Modulus.
mod :: SExpr -> SExpr -> SExpr
mod x y = smtFun "mod" [x,y]

-- | Is the number divisible by the given constante.
divisible :: SExpr -> Integer -> SExpr
divisible x n = List [ smtFam "divisible" [n], x ]

-- | Division of real numbers.
realDiv :: SExpr -> SExpr -> SExpr
realDiv x y = smtFun "/" [x,y]

-- | Bit vector concatenation.
concat :: SExpr -> SExpr -> SExpr
concat x y = smtFun "concat" [x,y]

-- | Extract a sub-sequence of a bit vector.
extract :: SExpr -> Integer -> Integer -> SExpr
extract x y z = List [ smtFam "extract" [y,z], x ]

-- | Bitwise negation.
bvNot :: SExpr -> SExpr
bvNot x = smtFun "bvnot" [x]

-- | Bitwise conjuction.
bvAnd :: SExpr -> SExpr -> SExpr
bvAnd x y = smtFun "bvand" [x,y]

-- | Bitwsie disjucntion.
bvOr :: SExpr -> SExpr -> SExpr
bvOr x y = smtFun "bvor" [x,y]

-- | Bit vector arithmetic negation.
bvNeg :: SExpr -> SExpr
bvNeg x = smtFun "bvneg" [x]

-- | Addition of bit vectors.
bvAdd :: SExpr -> SExpr -> SExpr
bvAdd x y = smtFun "bvadd" [x,y]

-- | Multiplication of bit vectors.
bvMul :: SExpr -> SExpr -> SExpr
bvMul x y = smtFun "bvmul" [x,y]

-- | Bit vector unsigned division.
bvUDiv :: SExpr -> SExpr -> SExpr
bvUDiv x y = smtFun "bvudiv" [x,y]

-- | Bit vector unsigned reminder.
bvURem :: SExpr -> SExpr -> SExpr
bvURem x y = smtFun "bvurem" [x,y]

-- | Shift left.
bvShl :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvShl x y = smtFun "bvshl" [x,y]

-- | Logical shift right.
bvLShr :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvLShr x y = smtFun "bvshr" [x,y]

-- | Get an elemeent of an array.
select :: SExpr {- ^ array -} -> SExpr {- ^ index -} -> SExpr
select x y = smtFun "select" [x,y]

-- | Update an array
store :: SExpr {- ^ array -}     ->
         SExpr {- ^ index -}     ->
         SExpr {- ^ new value -} ->
         SExpr
store x y z = smtFun "store" [x,y,z]



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








