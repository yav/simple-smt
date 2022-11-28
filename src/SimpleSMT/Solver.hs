{-# LANGUAGE OverloadedStrings #-}

-- | A module for interacting with an SMT solver, using SmtLib-2 format.
module SimpleSMT.Solver
    -- * Basic Solver Interface
  ( Solver(..)
  , Backend(..)
  , initSolverWith
  , command
  , ackCommand
  , simpleCommand
  , simpleCommandMaybe
  , loadFile
    -- * Common SmtLib-2 Commands
  , setLogic
  , setLogicMaybe
  , setOption
  , setOptionMaybe
  , produceUnsatCores
  , push
  , pushMany
  , pop
  , popMany
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
  , getExprs
  , getExpr
  , getConsts
  , getConst
  , getUnsatCore
  ) where

import SimpleSMT.SExpr
import Prelude hiding (not, and, or, abs, div, mod, concat, const, log)
import qualified Control.Exception as X
import Data.ByteString.Builder (Builder, toLazyByteString, lazyByteString)
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.IORef (IORef, newIORef, atomicModifyIORef)

data Backend = Backend {
  send :: Builder -> IO LBS.ByteString
  -- ^ Send a command to the backend.
  }

type Queue = IORef Builder

-- | Push a command on the solver's queue of commands to evaluate.
-- The command must not produce any output when evaluated, unless it is the last
-- command added before the queue is flushed.
putQueue :: Queue -> SExpr -> IO ()
putQueue q expr = atomicModifyIORef q $ \cmds ->
  (cmds <> renderSExpr expr, ())

-- | Empty the queue of commands to evaluate and return its content as a bytestring
-- builder.
flushQueue :: Queue -> IO Builder
flushQueue q = atomicModifyIORef q $ \cmds ->
    (mempty, cmds)

data Solver = Solver
  { backend :: Backend
  -- ^ The backend processing the commands.
  , queue :: Maybe Queue
  -- ^ A queue to write commands that are to be sent to the solver lazily.
  , log :: LBS.ByteString -> IO ()
  -- ^ The function used for logging the solver's activity.
  }

sendSolver :: Solver -> Builder -> IO SExpr
sendSolver solver cmd = do
  log solver $ "[send] " <> toLazyByteString cmd
  resp <- send (backend solver) cmd
  case parseSExpr resp of
    Nothing -> do
      log solver $ "[error] failed to parse solver output:\n" <> resp
      fail $
        unlines ["Unexpected response from the SMT solver:", "parsing failed"]
    Just (expr, _) -> do
      log solver $ "[recv] " <> toLazyByteString (renderSExpr expr)
      return expr

-- | Create a new solver and initialize it with some options so that it behaves
-- correctly for our use.
initSolverWith ::
     Backend
  -- | whether to enable lazy mode
  -> Bool
  -- | function for logging the solver's activity
  -> (LBS.ByteString -> IO ())
  -> IO Solver
initSolverWith solverBackend lazy logger = do
  solverQueue <- if lazy then do
      ref <- newIORef mempty
      return $ Just ref
    else return Nothing
  let solver = Solver solverBackend solverQueue logger
  if lazy then
      return ()
    else
      -- this should not be enabled when the queue is used, as it messes with parsing
      -- the outputs of commands that are actually interesting
      -- TODO checking for correctness and enabling laziness can be made compatible
      -- but it would require the solver backends to return list of s-expressions
      -- alternatively, we may consider that the user wanting both features should
      -- implement their own backend that deals with this
      setOption solver ":print-success" "true"
  setOption solver ":produce-models" "true"
  return solver


-- | Have the solver evaluate a command in SExpr format.
-- This forces the queued commands to be evaluated as well, but their results are
-- *not* checked for correctness.
command :: Solver -> SExpr -> IO SExpr
command solver expr = do
  let cmd = renderSExpr expr
  sendSolver solver =<<
    case queue solver of
      Nothing -> return $ cmd
      Just q -> (<> renderSExpr expr) <$> flushQueue q

-- | Load the contents of a file.
loadFile :: Solver -> FilePath -> IO ()
loadFile solver file =
  lazyByteString <$> LBS.readFile file >>= sendSolver solver >> return ()

-- | A command with no interesting result.
-- In eager mode, the result is checked for correctness.
-- In lazy mode, (unless the queue is flushed and evaluated
-- right after) the command must not produce any output when evaluated, and
-- its output is thus in particular not checked for correctness.
ackCommand :: Solver -> SExpr -> IO ()
ackCommand solver expr =
  case queue solver of
    Nothing -> do
      res <- sendSolver solver $ renderSExpr expr
      case res of
        Atom "success" -> return ()
        _  -> fail $ unlines [
          "Unexpected result from the SMT solver:"
          , "  Expected: success"
          , "  Result: " ++ showsSExpr res ""
          ]
    Just q -> putQueue q expr

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
declareFun proc f as' r =
  do ackCommand proc $ fun "declare-fun" [ Atom f, List as', r ]
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
defineFun proc f as' t e =
  do ackCommand proc $ fun "define-fun"
                     $ [ Atom f, List [ List [const x,a] | (x,a) <- as' ], t, e]
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
defineFunRec proc f as' t e =
  do let fs = const f
     ackCommand proc $ fun "define-fun-rec"
                     $ [ Atom f, List [ List [const x,a] | (x,a) <- as' ], t, e fs]
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
