{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
-- | A module for interacting with an SMT solver, using SmtLib-2 format.
module SimpleSMT.Solver
  (
    -- * Basic Solver Interface
    Solver(..)
  , newSolver
  , newSolverNotify
  , ackCommand
  , simpleCommand
  , simpleCommandMaybe
  , loadFile
  , loadString

    -- ** Logging and Debugging
  , Logger(..)
  , newLogger
  , withLogLevel
  , logMessageAt
  , logIndented

    -- * Common SmtLib-2 Commands
  , setLogic, setLogicMaybe
  , setOption, setOptionMaybe
  , produceUnsatCores
  , push, pushMany
  , pop, popMany
  , inNewScope
  , declare
  , declareFun
  , declareDatatype
  , define
  , defineFun
  , defineFunRec
  , defineFunsRec
  , assert
  , check
  , getExprs, getExpr
  , getConsts, getConst
  , getUnsatCore
  ) where

import SimpleSMT.SExpr
import Prelude hiding (not, and, or, abs, div, mod, concat, const)
import qualified Prelude as P
import Data.Char(isSpace, isDigit)
import Data.List(unfoldr,intersperse)
import Data.Bits(testBit)
import Data.IORef(newIORef, atomicModifyIORef, modifyIORef', readIORef,
                  writeIORef)
import System.Process(runInteractiveProcess, waitForProcess, terminateProcess)
import System.IO (hFlush, hGetLine, hGetContents, hPutStrLn, stdout, hClose)
import System.Exit(ExitCode)
import qualified Control.Exception as X
import Control.Concurrent(forkIO)
import Control.Monad(forever,when,void)
import Text.Read(readMaybe)
import Data.Ratio((%), numerator, denominator)
import Numeric(showHex, readHex, showFFloat)

-- | An interactive solver process.
data Solver = Solver
  { command   :: SExpr -> IO SExpr
    -- ^ Send a command to the solver.

  , stop :: IO ExitCode
    -- ^ Wait for the solver to finish and exit gracefully.

  , forceStop :: IO ExitCode
    -- ^ Terminate the solver without waiting for it to finish.
  }


-- | Start a new solver process.
newSolver :: String       {- ^ Executable -}            ->
             [String]     {- ^ Arguments -}             ->
             Maybe Logger {- ^ Optional logging here -} ->
             IO Solver
newSolver n xs l = newSolverNotify n xs l Nothing

newSolverNotify ::
  String        {- ^ Executable -}            ->
  [String]      {- ^ Arguments -}             ->
  Maybe Logger  {- ^ Optional logging here -} ->
  Maybe (ExitCode -> IO ()) {- ^ Do this when the solver exits -} ->
  IO Solver
newSolverNotify exe opts mbLog mbOnExit =
  do (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing

     let info a = case mbLog of
                    Nothing -> return ()
                    Just l  -> logMessage l a

     _ <- forkIO $ forever (do errs <- hGetLine hErr
                               info ("[stderr] " ++ errs))
                    `X.catch` \X.SomeException {} -> return ()

     case mbOnExit of
       Nothing -> pure ()
       Just this -> void (forkIO (this =<< waitForProcess h))

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

         waitAndCleanup =
           do ec <- waitForProcess h
              X.catch (do hClose hIn
                          hClose hOut
                          hClose hErr)
                      (\ex -> info (show (ex::X.IOException)))
              return ec

         forceStop = terminateProcess h *> waitAndCleanup

         stop =
           do cmd (List [Atom "exit"])
                `X.catch` (\X.SomeException{} -> pure ())
              waitAndCleanup

         solver = Solver { .. }

     setOption solver ":print-success" "true"
     setOption solver ":produce-models" "true"

     return solver


-- | Load the contents of a file.
loadFile :: Solver -> FilePath -> IO ()
loadFile s file = loadString s =<< readFile file

-- | Load a raw SMT string.
loadString :: Solver -> String -> IO ()
loadString s str = go (dropComments str)
  where
  go txt
    | all isSpace txt = return ()
    | otherwise =
      case readSExpr txt of
        Just (e,rest) -> command s e >> go rest
        Nothing       -> fail $ unlines [ "Failed to parse SMT file."
                                        , txt
                                        ]

  dropComments = unlines . map dropComment . lines
  dropComment xs = case break (== ';') xs of
                     (as,_:_) -> as
                     _ -> xs




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

-- | Run a command and return True if successful, and False if unsupported.
-- This is useful for setting options that unsupported by some solvers, but used
-- by others.
simpleCommandMaybe :: Solver -> [String] -> IO Bool
simpleCommandMaybe proc c =
  do res <- command proc (List (map Atom c))
     case res of
       Atom "success"     -> return True
       Atom "unsupported" -> return False
       _                  -> fail $ unlines
                                      [ "Unexpected result from the SMT solver:"
                                      , "  Expected: success or unsupported"
                                      , "  Result: " ++ showsSExpr res ""
                                      ]


-- | Set a solver option.
setOption :: Solver -> String -> String -> IO ()
setOption s x y = simpleCommand s [ "set-option", x, y ]

-- | Set a solver option, returning False if the option is unsupported.
setOptionMaybe :: Solver -> String -> String -> IO Bool
setOptionMaybe s x y = simpleCommandMaybe s [ "set-option", x, y ]

-- | Set the solver's logic.  Usually, this should be done first.
setLogic :: Solver -> String -> IO ()
setLogic s x = simpleCommand s [ "set-logic", x ]


-- | Set the solver's logic, returning False if the logic is unsupported.
setLogicMaybe :: Solver -> String -> IO Bool
setLogicMaybe s x = simpleCommandMaybe s [ "set-logic", x ]

-- | Request unsat cores.  Returns if the solver supports them.
produceUnsatCores :: Solver -> IO Bool
produceUnsatCores s = setOptionMaybe s ":produce-unsat-cores" "true"

-- | Checkpoint state.  A special case of 'pushMany'.
push :: Solver -> IO ()
push proc = pushMany proc 1

-- | Restore to last check-point.  A special case of 'popMany'.
pop :: Solver -> IO ()
pop proc = popMany proc 1

-- | Push multiple scopes.
pushMany :: Solver -> Integer -> IO ()
pushMany proc n = simpleCommand proc [ "push", show n ]

-- | Pop multiple scopes.
popMany :: Solver -> Integer -> IO ()
popMany proc n = simpleCommand proc [ "pop", show n ]

-- | Execute the IO action in a new solver scope (push before, pop after)
inNewScope :: Solver -> IO a -> IO a
inNewScope s m =
  do push s
     m `X.finally` pop s



-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns an the declared name as a constant expression.
declare :: Solver -> String -> SExpr -> IO SExpr
declare proc f t = declareFun proc f [] t

-- | Declare a function or a constant.
-- For convenience, returns an the declared name as a constant expression.
declareFun :: Solver -> String -> [SExpr] -> SExpr -> IO SExpr
declareFun proc f as r =
  do ackCommand proc $ fun "declare-fun" [ Atom f, List as, r ]
     return (const f)

-- | Declare an ADT using the format introduced in SmtLib 2.6.
declareDatatype ::
  Solver ->
  String {- ^ datatype name -} ->
  [String] {- ^ sort parameters -} ->
  [(String, [(String, SExpr)])] {- ^ constructors -} ->
  IO ()
declareDatatype proc t [] cs =
  ackCommand proc $
    fun "declare-datatype" $
      [ Atom t
      , List [ List (Atom c : [ List [Atom s, argTy] | (s, argTy) <- args]) | (c, args) <- cs ]
      ]
declareDatatype proc t ps cs =
  ackCommand proc $
    fun "declare-datatype" $
      [ Atom t
      , fun "par" $
          [ List (map Atom ps)
          , List [ List (Atom c : [ List [Atom s, argTy] | (s, argTy) <- args]) | (c, args) <- cs ]
          ]
      ]


-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns the defined name as a constant expression.
define :: Solver ->
          String {- ^ New symbol -} ->
          SExpr  {- ^ Symbol type -} ->
          SExpr  {- ^ Symbol definition -} ->
          IO SExpr
define proc f t e = defineFun proc f [] t e

-- | Define a function or a constant.
-- For convenience, returns an the defined name as a constant expression.
defineFun :: Solver ->
             String           {- ^ New symbol -} ->
             [(String,SExpr)] {- ^ Parameters, with types -} ->
             SExpr            {- ^ Type of result -} ->
             SExpr            {- ^ Definition -} ->
             IO SExpr
defineFun proc f as t e =
  do ackCommand proc $ fun "define-fun"
                     $ [ Atom f, List [ List [const x,a] | (x,a) <- as ], t, e]
     return (const f)

-- | Define a recursive function or a constant.  For convenience,
-- returns an the defined name as a constant expression.  This body
-- takes the function name as an argument.
defineFunRec :: Solver ->
                String           {- ^ New symbol -} ->
                [(String,SExpr)] {- ^ Parameters, with types -} ->
                SExpr            {- ^ Type of result -} ->
                (SExpr -> SExpr) {- ^ Definition -} ->
                IO SExpr
defineFunRec proc f as t e =
  do let fs = const f
     ackCommand proc $ fun "define-fun-rec"
                     $ [ Atom f, List [ List [const x,a] | (x,a) <- as ], t, e fs]
     return fs

-- | Define a recursive function or a constant.  For convenience,
-- returns an the defined name as a constant expression.  This body
-- takes the function name as an argument.
defineFunsRec :: Solver ->
                 [(String, [(String,SExpr)], SExpr, SExpr)] ->
                 IO ()
defineFunsRec proc ds = ackCommand proc $ fun "define-funs-rec" [ decls, bodies ]
  where
    oneArg (f, args, t, _) = List [ Atom f, List [ List [const x,a] | (x,a) <- args ], t]
    decls  = List (map oneArg ds)
    bodies = List (map (\(_, _, _, body) -> body) ds)


-- | Assume a fact.
assert :: Solver -> SExpr -> IO ()
assert proc e = ackCommand proc $ fun "assert" [e]

-- | Check if the current set of assertion is consistent.
check :: Solver -> IO Result
check proc = do
  res <- command proc (List [Atom "check-sat"])
  case res of
    Atom "unsat" -> return Unsat
    Atom "unknown" -> return Unknown
    Atom "sat" -> return Sat
    _ ->
      fail $
      unlines
        [ "Unexpected result from the SMT solver:"
        , "  Expected: unsat, unknown, or sat"
        , "  Result: " ++ showsSExpr res ""
        ]

-- | Get the values of some s-expressions.
-- Only valid after a 'Sat' result.
getExprs :: Solver -> [SExpr] -> IO [(SExpr, Value)]
getExprs proc vals =
  do res <- command proc $ List [ Atom "get-value", List vals ]
     case res of
       List xs -> mapM getAns xs
       _ -> fail $ unlines
                 [ "Unexpected response from the SMT solver:"
                 , "  Exptected: a list"
                 , "  Result: " ++ showsSExpr res ""
                 ]
  where
  getAns expr =
    case expr of
      List [ e, v ] -> return (e, sexprToVal v)
      _             -> fail $ unlines
                            [ "Unexpected response from the SMT solver:"
                            , "  Expected: (expr val)"
                            , "  Result: " ++ showsSExpr expr ""
                            ]

-- | Get the values of some constants in the current model.
-- A special case of 'getExprs'.
-- Only valid after a 'Sat' result.
getConsts :: Solver -> [String] -> IO [(String, Value)]
getConsts proc xs =
  do ans <- getExprs proc (map Atom xs)
     return [ (x,e) | (Atom x, e) <- ans ]


-- | Get the value of a single expression.
getExpr :: Solver -> SExpr -> IO Value
getExpr proc x =
  do [ (_,v) ] <- getExprs proc [x]
     return v

-- | Get the value of a single constant.
getConst :: Solver -> String -> IO Value
getConst proc x = getExpr proc (Atom x)

-- | Returns the names of the (named) formulas involved in a contradiction.
getUnsatCore :: Solver -> IO [String]
getUnsatCore s =
  do res <- command s $ List [ Atom "get-unsat-core" ]
     case res of
       List xs -> mapM fromAtom xs
       _       -> unexpected "a list of atoms" res
  where
  fromAtom x =
    case x of
      Atom a -> return a
      _      -> unexpected "an atom" x

  unexpected x e =
    fail $ unlines [ "Unexpected response from the SMT Solver:"
                   , "  Expected: " ++ x
                   , "  Result: " ++ showsSExpr e ""
                   ]
--------------------------------------------------------------------------------

-- | Log messages with minimal formatting. Mostly for debugging.
data Logger = Logger
  { logMessage :: String -> IO ()
    -- ^ Log a message.

  , logLevel   :: IO Int

  , logSetLevel:: Int -> IO ()

  , logTab     :: IO ()
    -- ^ Increase indentation.

  , logUntab   :: IO ()
    -- ^ Decrease indentation.
  }

-- | Run an IO action with the logger set to a specific level, restoring it when
-- done.
withLogLevel :: Logger -> Int -> IO a -> IO a
withLogLevel Logger { .. } l m =
  do l0 <- logLevel
     X.bracket_ (logSetLevel l) (logSetLevel l0) m

logIndented :: Logger -> IO a -> IO a
logIndented Logger { .. } = X.bracket_ logTab logUntab

-- | Log a message at a specific log level.
logMessageAt :: Logger -> Int -> String -> IO ()
logMessageAt logger l msg = withLogLevel logger l (logMessage logger msg)

-- | A simple stdout logger.  Shows only messages logged at a level that is
-- greater than or equal to the passed level.
newLogger :: Int -> IO Logger
newLogger l =
  do tab <- newIORef 0
     lev <- newIORef 0
     let logLevel    = readIORef lev
         logSetLevel = writeIORef lev

         shouldLog m =
           do cl <- logLevel
              when (cl >= l) m

         logMessage x = shouldLog $
           do let ls = lines x
              t <- readIORef tab
              putStr $ unlines [ replicate t ' ' ++ l | l <- ls ]
              hFlush stdout

         logTab   = shouldLog (modifyIORef' tab (+ 2))
         logUntab = shouldLog (modifyIORef' tab (subtract 2))
     return Logger { .. }
