-- | A module for interacting with an SMT solver, using SmtLib-2 format.
module SimpleSMT.Solver
    -- * Basic Solver Interface
  ( Backend(..)
  , Solver(..)
  , ackCommand
  , simpleCommand
  , simpleCommandMaybe
  , loadFile
  , loadString
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
import Prelude hiding (not, and, or, abs, div, mod, concat, const)
import qualified Control.Exception as X
import qualified Data.ByteString.Char8 as BS
import Data.Char(isSpace)
import System.Exit(ExitCode)

class Backend s where
  send :: s -> BS.ByteString -> IO SExpr
    -- ^ Send a command to the solver.
  stop :: s -> IO ExitCode
    -- ^ Wait for the solver to finish and exit gracefully.

data Backend s =>
     Solver s =
  Solver
    { backend :: s
    }  

instance Backend s => Backend (Solver s) where
  send solver = send (backend solver)
  stop solver = stop (backend solver)

command :: Backend s => Solver s -> SExpr -> IO SExpr
command solver expr = do
  let cmd = serializeSExpr expr
  send solver cmd
  
-- | Load the contents of a file.
loadFile :: Backend s => Solver s -> FilePath -> IO ()
loadFile s file = loadString s =<< readFile file

-- | Load a raw SMT string.
loadString :: Backend s => Solver s -> String -> IO ()
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
                     (as',_:_) -> as'
                     _ -> xs




-- | A command with no interesting result.
ackCommand :: Backend s => Solver s -> SExpr -> IO ()
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
simpleCommand :: Backend s => Solver s -> [String] -> IO ()
simpleCommand proc = ackCommand proc . List . map Atom

-- | Run a command and return True if successful, and False if unsupported.
-- This is useful for setting options that unsupported by some solvers, but used
-- by others.
simpleCommandMaybe :: Backend s => Solver s -> [String] -> IO Bool
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
setOption :: Backend s => Solver s -> String -> String -> IO ()
setOption s x y = simpleCommand s [ "set-option", x, y ]

-- | Set a solver option, returning False if the option is unsupported.
setOptionMaybe :: Backend s => Solver s -> String -> String -> IO Bool
setOptionMaybe s x y = simpleCommandMaybe s [ "set-option", x, y ]

-- | Set the solver's logic.  Usually, this should be done first.
setLogic :: Backend s => Solver s -> String -> IO ()
setLogic s x = simpleCommand s [ "set-logic", x ]


-- | Set the solver's logic, returning False if the logic is unsupported.
setLogicMaybe :: Backend s => Solver s -> String -> IO Bool
setLogicMaybe s x = simpleCommandMaybe s [ "set-logic", x ]

-- | Request unsat cores.  Returns if the solver supports them.
produceUnsatCores :: Backend s => Solver s -> IO Bool
produceUnsatCores s = setOptionMaybe s ":produce-unsat-cores" "true"

-- | Checkpoint state.  A special case of 'pushMany'.
push :: Backend s => Solver s -> IO ()
push proc = pushMany proc 1

-- | Restore to last check-point.  A special case of 'popMany'.
pop :: Backend s => Solver s -> IO ()
pop proc = popMany proc 1

-- | Push multiple scopes.
pushMany :: Backend s => Solver s -> Integer -> IO ()
pushMany proc n = simpleCommand proc [ "push", show n ]

-- | Pop multiple scopes.
popMany :: Backend s => Solver s -> Integer -> IO ()
popMany proc n = simpleCommand proc [ "pop", show n ]

-- | Execute the IO action in a new solver scope (push before, pop after)
inNewScope :: Backend s => Solver s -> IO a -> IO a
inNewScope s m =
  do push s
     m `X.finally` pop s



-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns an the declared name as a constant expression.
declare :: Backend s => Solver s -> String -> SExpr -> IO SExpr
declare proc f t = declareFun proc f [] t

-- | Declare a function or a constant.
-- For convenience, returns an the declared name as a constant expression.
declareFun :: Backend s => Solver s -> String -> [SExpr] -> SExpr -> IO SExpr
declareFun proc f as' r =
  do ackCommand proc $ fun "declare-fun" [ Atom f, List as', r ]
     return (const f)

-- | Declare an ADT using the format introduced in SmtLib 2.6.
declareDatatype ::
  Backend s => Solver s ->
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
define :: Backend s => Solver s ->
          String {- ^ New symbol -} ->
          SExpr  {- ^ Symbol type -} ->
          SExpr  {- ^ Symbol definition -} ->
          IO SExpr
define proc f t e = defineFun proc f [] t e

-- | Define a function or a constant.
-- For convenience, returns an the defined name as a constant expression.
defineFun :: Backend s => Solver s ->
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
defineFunRec :: Backend s => Solver s ->
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
defineFunsRec :: Backend s => Solver s ->
                 [(String, [(String,SExpr)], SExpr, SExpr)] ->
                 IO ()
defineFunsRec proc ds = ackCommand proc $ fun "define-funs-rec" [ decls, bodies ]
  where
    oneArg (f, args, t, _) = List [ Atom f, List [ List [const x,a] | (x,a) <- args ], t]
    decls  = List (map oneArg ds)
    bodies = List (map (\(_, _, _, body) -> body) ds)


-- | Assume a fact.
assert :: Backend s => Solver s -> SExpr -> IO ()
assert proc e = ackCommand proc $ fun "assert" [e]

-- | Check if the current set of assertion is consistent.
check :: Backend s => Solver s -> IO Result
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
getExprs :: Backend s => Solver s -> [SExpr] -> IO [(SExpr, Value)]
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
getConsts :: Backend s => Solver s -> [String] -> IO [(String, Value)]
getConsts proc xs =
  do ans <- getExprs proc (map Atom xs)
     return [ (x,e) | (Atom x, e) <- ans ]


-- | Get the value of a single expression.
getExpr :: Backend s => Solver s -> SExpr -> IO Value
getExpr proc x =
  do [ (_,v) ] <- getExprs proc [x]
     return v

-- | Get the value of a single constant.
getConst :: Backend s => Solver s -> String -> IO Value
getConst proc x = getExpr proc (Atom x)

-- | Returns the names of the (named) formulas involved in a contradiction.
getUnsatCore :: Backend s => Solver s -> IO [String]
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
