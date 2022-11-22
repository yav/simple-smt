{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ViewPatterns      #-}
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
import Data.List.Extra ((!?))
import Data.Int (Int64)
import Data.IORef (IORef, newIORef, atomicModifyIORef)
import Data.Tuple (swap)
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
    , response :: IORef LBS.ByteString
    -- ^ A buffer holding the solver's response.
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
  solverResponse <- newIORef =<< (LBS.hGetContents $ getStdout solverProcess)
  return $ SolverProcess solverProcess solverErrorReader solverResponse
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
toBackend :: SolverProcess -> Solver.Backend
toBackend solver =
  Solver.Backend $ \cmd -> do
    hPutBuilder (getStdin $ process solver) cmd
    getNextOutput $ response solver
  where
    getNextOutput :: IORef LBS.ByteString -> IO LBS.ByteString
    getNextOutput solverResponse = atomicModifyIORef solverResponse $ \buffer ->
      let parLeftIndices = LBS.elemIndices '(' buffer in
      let parRightIndices = LBS.elemIndices ')' buffer in
      case findEnd 0 parLeftIndices parRightIndices of
        -- if we can't match parenthesis, we just return the whole buffer
        -- the parsing error will be thrown in the common interface
        Nothing -> (mempty, buffer)
        -- otherwise, split the buffer after the first well-parenthesized word
        Just end -> swap $ LBS.splitAt end buffer

    -- given a current depth, and list of indices of the appearances of '(' and ')'
    -- output the index of the ')' corresponding to the end of the first
    -- well-parenthesized word
    findEnd :: Int -> [Int64] -> [Int64] -> Maybe Int64
    findEnd 0 [] (_ : _) = Nothing
    findEnd depth [] moreRight = moreRight !? (depth - 1)
    findEnd 0 (n : _) (m : _) | n > m = Nothing
    findEnd 1 (n : _) (m : _) | n > m = Just m
    findEnd depth (n : moreLeft) (m : moreRight) | n > m = findEnd (depth - 1) (n : moreLeft) moreRight
                                                 | otherwise = findEnd (depth + 1) moreLeft (m : moreRight)
    findEnd _ _ _ = Nothing

