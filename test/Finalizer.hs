{-# OPTIONS_GHC -O2 #-}

module Main (main) where

import Control.Concurrent.MVar
  ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Exception (evaluate)
import Control.Monad (unless, when)
import System.Environment (getArgs, getExecutablePath)
import System.Exit (ExitCode)
import System.IO (hFlush, hPutStrLn, isEOF, stderr, stdout)
import System.Mem (performGC)
import System.Timeout (timeout)

import SimpleSMT


eofMessage :: String
eofMessage = "fake solver: stdin closed"


prematureFinalizerWindow :: Int
prematureFinalizerWindow = 50000


operationTimeout :: Int
operationTimeout = 2000000


main :: IO ()
main =
  do args <- getArgs
     case args of
       ["--solver"] -> fakeSolver
       _ -> testFinalizer


testFinalizer :: IO ()
testFinalizer =
  do exe <- getExecutablePath

     -- Keeping projected Solver operations alive must keep the external
     -- process alive too.
     progress "Test 1: live solver operations prevent finalization"
     exited <- newEmptyMVar
     solver <- within "starting the first solver" $
       newSolverNotify exe ["--solver"] Nothing
         (Just (\ec ->
                  do progress ("First solver exited: " ++ show ec)
                     putMVar exited ec))
     run <- evaluate (command solver)
     finish <- evaluate (stop solver)

     progress "  Forcing GC while projected operations are still live"
     performGC

     prematureExit <- timeout prematureFinalizerWindow (takeMVar exited)
     case prematureExit of
       Just _ -> fail "Solver finalizer ran while its operations were live"
       Nothing -> progress "  Solver remained alive"

     progress "  Sending check-sat after GC"
     result <- within "waiting for check-sat" $
       run (List [Atom "check-sat"])
     unless (result == Atom "sat") $
       fail ("Unexpected check-sat response: " ++ show result)
     progress "  Stopping the first solver explicitly"
     _ <- within "stopping the first solver" finish

     -- Once the Solver and its operations are unreachable, its finalizer
     -- must close stdin and allow the external process to exit.
     progress "Test 2: unreachable solver is finalized"
     finalized <- newEmptyMVar
     sawEOF <- newEmptyMVar
     within "using the second solver" $
       useAndForgetSolver exe sawEOF finalized
     progress "  Dropped the solver; forcing GC"
     performGC

     finalResult <- timeout operationTimeout $
       do takeMVar sawEOF
          takeMVar finalized
     case finalResult of
       Just _ -> progress "  Solver observed EOF and exited"
       Nothing ->
         fail "Solver finalizer did not close stdin and terminate the process"

     progress "Finalizer tests passed"


{-# NOINLINE useAndForgetSolver #-}
useAndForgetSolver :: FilePath -> MVar () -> MVar ExitCode -> IO ()
useAndForgetSolver exe sawEOF exited =
  do let logger =
           noSolverLogger
             { solverLogStdErr = \message ->
                 when (message == eofMessage) $
                   do progress "  Fake solver observed EOF"
                      putMVar sawEOF ()
             }
         config =
           (defaultConfig exe ["--solver"])
             { solverOnExit =
                 Just (\ec ->
                         do progress ("  Second solver exited: " ++ show ec)
                            putMVar exited ec)
             , solverLogger = logger
             }
     solver <- newSolverWithConfig config
     result <- command solver (List [Atom "check-sat"])
     unless (result == Atom "sat") $
       fail ("Unexpected check-sat response: " ++ show result)


fakeSolver :: IO ()
fakeSolver =
  do eof <- isEOF
     if eof
       then hPutStrLn stderr eofMessage
       else do request <- getLine
               case request of
                 "(exit)" -> pure ()
                 "(check-sat)" -> respond "sat" >> fakeSolver
                 _ -> respond "success" >> fakeSolver
  where
  respond response =
    do putStrLn response
       hFlush stdout


within :: String -> IO a -> IO a
within description action =
  do result <- timeout operationTimeout action
     case result of
       Just value -> pure value
       Nothing -> fail ("Timed out " ++ description)


progress :: String -> IO ()
progress message =
  do putStrLn message
     hFlush stdout
