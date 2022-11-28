{-# LANGUAGE OverloadedStrings #-}
module SimpleSMT.Tests.Solver (tests, testBackend) where

import qualified SimpleSMT.SExpr as SExpr
import qualified SimpleSMT.Solver as Solver
import qualified SimpleSMT.Solver.Process as Process
import qualified SimpleSMT.Tests.Sources as Src

import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.ByteString.Builder (toLazyByteString)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (unfoldr, isPrefixOf)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Solver"
    [ testBackend "dummy" $ \todo -> do
        backend <- dummy
        todo backend,
      testBackend "process" $ \todo -> Process.with "z3" ["-in"] (const $ return ()) $ todo . Process.toBackend

    ]

-- | A simple backend that's always successful.
dummy :: IO Solver.Backend
dummy = do
  printSuccess <- newIORef False
  return $
    Solver.Backend $ \cmd
      -- LBS.putStrLn $ toLazyByteString cmd
     -> do
      res <-
        process printSuccess $ unfoldr SExpr.parseSExpr $ toLazyByteString cmd
      -- LBS.putStrLn res
      return res
  where
    process _ [] = return ""
    process printSuccess (expr:exprs) = do
      res <-
        case expr of
          SExpr.List [SExpr.Atom "check-sat"] -> return "unknown"
          SExpr.List [SExpr.Atom "set-option", SExpr.Atom ":print-success", SExpr.Atom value] -> do
            let b = value == "true"
            writeIORef printSuccess b
            return $
              if b
                then "success"
                else ""
          SExpr.List ((SExpr.Atom "error"):_) -> return "error"
          SExpr.List ((SExpr.Atom foo):_)
            | "get-" `isPrefixOf` foo -> return "()"
          SExpr.List _ -> do
            printSuccess' <- readIORef printSuccess
            return $
              if printSuccess'
                then "success"
                else ""
          _ -> return "error"
      ((res <> "\n") <>) <$> process printSuccess exprs

testBackend ::
     String -> ((Solver.Backend -> Assertion) -> Assertion) -> TestTree
testBackend name with =
  testGroup name $ do
    lazyMode <- [False, True]
    return $
      testGroup
        (if lazyMode
           then "lazy"
           else "eager") $ do
        source <- Src.sources
        return $
          testCase (Src.name source) $
          with $ \backend -> do
            solver <- Solver.initSolverWith backend lazyMode LBS.putStrLn
            Src.run source solver
