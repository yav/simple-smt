{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
module SimpleSMT.Solver.Process
    -- * Basic Solver Interface
  ( SolverProcess
  , newSolverProcess
  , newSolverProcessNotify
  -- ** Logging and Debugging
  , Logger(..)
  , newLogger
  , withLogLevel
  , logMessageAt
  , logIndented
  ) where

import SimpleSMT.Solver (Backend(..), Solver(..), setOption)
import SimpleSMT.SExpr (SExpr(..), parseSExpr, showsSExpr) 

import Control.Monad(forever,when,void)
import Control.Concurrent(forkIO)
import qualified Control.Exception as X
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.IORef(newIORef, atomicModifyIORef, modifyIORef', readIORef,
                  writeIORef)
import Data.List(unfoldr)
import System.Exit(ExitCode)
import System.Process(runInteractiveProcess, waitForProcess, terminateProcess)
import System.IO (hFlush, stdout, hClose)

data SolverProcess = SolverProcess
  { command   :: LBS.ByteString -> IO SExpr 
    -- ^ Send a command to the solver.

  , waitStop :: IO ExitCode
    -- ^ Wait for the solver to finish and exit gracefully.

  , forceStop :: IO ExitCode
    -- ^ Terminate the solver without waiting for it to finish.
  }

instance Backend SolverProcess where
  send solver cmd = command solver cmd

-- | Start a new solver process.
newSolverProcess :: String       {- ^ Executable -}            ->
             [String]     {- ^ Arguments -}             ->
             Maybe Logger {- ^ Optional logging here -} ->
             IO (Solver SolverProcess)
newSolverProcess n xs l = newSolverProcessNotify n xs l Nothing

newSolverProcessNotify ::
  String        {- ^ Executable -}            ->
  [String]      {- ^ Arguments -}             ->
  Maybe Logger  {- ^ Optional logging here -} ->
  Maybe (ExitCode -> IO ()) {- ^ Do this when the solver exits -} ->
  IO (Solver SolverProcess)
newSolverProcessNotify exe opts mbLog mbOnExit = do
  (hIn, hOut, hErr, h) <- runInteractiveProcess exe opts Nothing Nothing
  let info a =
        case mbLog of
          Nothing -> return ()
          Just l -> logMessage l a
  _ <-
    forkIO $
    forever
      (do errs <- BS.hGetLine hErr
          info ("[stderr] " <> BS.unpack errs)) `X.catch` \X.SomeException {} -> return ()
  case mbOnExit of
    Nothing -> pure ()
    Just this -> void (forkIO (this =<< waitForProcess h))
  getResponse <- 
    do txt <- LBS.hGetContents hOut -- Read *all* output
       ref <- newIORef (unfoldr parseSExpr txt) -- Parse, and store result
       return $
         atomicModifyIORef ref $ \xs ->
           case xs of
             [] -> (xs, Nothing)
             y:ys -> (ys, Just y)
  let cmd txt = do
        info ("[send->] " <> LBS.unpack txt)
        LBS.hPutStrLn hIn txt
      command c = do
        cmd c
        mb <- getResponse
        case mb of
          Just res -> do
            info ("[<-recv] " <> showsSExpr res "")
            return res
          Nothing -> fail "Missing response from solver"
      waitAndCleanup = do
        ec <- waitForProcess h
        X.catch
          (do hClose hIn
              hClose hOut
              hClose hErr)
          (\ex -> info (show (ex :: X.IOException)))
        return ec
      forceStop = terminateProcess h *> waitAndCleanup
      waitStop = do
        cmd "(exit)" `X.catch` (\X.SomeException {} -> pure ())
        waitAndCleanup
      solver = Solver $ SolverProcess {..}
  setOption solver ":print-success" "true"
  setOption solver ":produce-models" "true"
  return solver

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
              putStr $ unlines [ replicate t ' ' ++ l' | l' <- ls ]
              hFlush stdout

         logTab   = shouldLog (modifyIORef' tab (+ 2))
         logUntab = shouldLog (modifyIORef' tab (subtract 2))
     return Logger { .. }
