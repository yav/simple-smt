{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
module SimpleSMT.Solver.Process
  ( SolverProcess(..)
  , new
  , wait
  , stop
  , with
  , toBackend
  ) where

import qualified SimpleSMT.Solver as Solver

import Control.Monad (forever)
import Control.Concurrent.Async (Async, async, cancel)
import qualified Control.Exception as X
import Data.ByteString.Builder (hPutBuilder)
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.IORef (newIORef)
import System.Exit(ExitCode)
import System.IO (Handle, hClose)
import qualified System.Process.Typed as P (proc)
import System.Process.Typed
  ( Process
  , getStderr
  , getStdin
  , getStdout
  , mkPipeStreamSpec
  , setStderr
  , setStdin
  , setStdout
  , startProcess
  , stopProcess
  , waitExitCode
  )

data SolverProcess =
  SolverProcess
    { process :: Process Handle Handle Handle
    -- ^ The process running the solver.
    , errorReader :: Async ()
    -- ^ A process reading the solver's error messages and logging them.
    }

-- | Run a solver as a process.
new ::
  -- | The command to run the solver.
  String ->
  -- | Arguments to pass to the solver's command.
  [String] ->
  -- | A function for logging the solver's creation, errors and termination.
  (BS.ByteString -> IO ()) -> IO SolverProcess
new exe args logger = do
  solverProcess <-
    startProcess $
    setStdin createLoggedPipe $
    setStdout createLoggedPipe $ setStderr createLoggedPipe $ P.proc exe args
  -- log error messages created by the backend
  solverErrorReader <-
    async $
    forever
      (do errs <- BS.hGetLine $ getStderr solverProcess
          logger $ "[stderr] " <> errs) `X.catch` \X.SomeException {} ->
      return ()
  return $ SolverProcess solverProcess solverErrorReader
  where
    createLoggedPipe =
      mkPipeStreamSpec $ \_ h ->
        return
          ( h
          , hClose h `X.catch` \ex ->
              logger $ BS.pack $ show (ex :: X.IOException))

-- | Wait for the process to exit and cleanup its resources.
wait :: SolverProcess -> IO ExitCode
wait solver = do
  cancel $ errorReader solver
  waitExitCode $ process solver

-- | Terminate the process, wait for it to actually exit and cleanup its resources.
stop :: SolverProcess -> IO ()
stop solver = do
  cancel $ errorReader solver
  stopProcess $ process solver

-- | Create a solver process, use it to make a computation and stop it.
with :: String -> [String] -> (BS.ByteString -> IO ()) -> (SolverProcess -> IO a) -> IO a
with exe args logger todo = do
  solverProcess <- new exe args logger
  result <- todo solverProcess
  stop solverProcess
  return result

-- | Make the solver process into a solver backend.
toBackend :: SolverProcess -> IO Solver.Backend
toBackend solver = do
  response <- (LBS.hGetContents $ getStdout $ process solver) >>= newIORef
  return $
    flip Solver.Backend response $ \cmd ->
      hPutBuilder (getStdin $ process solver) cmd
