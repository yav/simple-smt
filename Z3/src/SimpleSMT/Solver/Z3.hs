{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module SimpleSMT.Solver.Z3
  ( Handle (toBackend)
  , new
  , close
  , with
  ) where

import qualified SimpleSMT.Solver as Solver

import Control.Exception (bracket)
import Data.ByteString.Builder.Extra
  ( defaultChunkSize
  , smallChunkSize
  , toLazyByteStringWith
  , untrimmedStrategy
  )
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import qualified Data.Map as M
import Foreign.Ptr (Ptr)
import Foreign.ForeignPtr (ForeignPtr, newForeignPtr, finalizeForeignPtr)
import qualified Language.C.Inline as C
import qualified Language.C.Inline.Unsafe as CU
import qualified Language.C.Inline.Context as C
import qualified Language.C.Types as C

data LogicalContext

C.context
  (C.baseCtx <>
   C.fptrCtx <>
   C.bsCtx <>
   mempty
     { C.ctxTypesTable =
         M.singleton (C.TypeName "Z3_context") [t|Ptr LogicalContext|]
     })
C.include "z3.h"

data Handle = Handle
  { context :: ForeignPtr LogicalContext
    -- ^ A black-box representing the internal state of the solver.
  , toBackend :: Solver.Backend
    -- ^ Create a solver backend out of a Z3 instance.
  }

-- | Create a new solver instance.
new :: IO Handle
new = do
  let ctxFinalizer =
        [C.funPtr| void free_context(Z3_context ctx) {
                 Z3_del_context(ctx);
                 } |]
  ctx <-
    newForeignPtr ctxFinalizer
    =<< [CU.block| Z3_context {
                 Z3_config cfg = Z3_mk_config();
                 Z3_context ctx = Z3_mk_context(cfg);
                 Z3_del_config(cfg);
                 return ctx;
                 } |]
  return $ Handle { context = ctx, toBackend = toBackend' ctx }

toBackend' :: ForeignPtr LogicalContext -> Solver.Backend
toBackend' ctx =
  Solver.Backend $ \cmd -> do
    let cmd' =
          LBS.toStrict $
          toLazyByteStringWith
            (untrimmedStrategy smallChunkSize defaultChunkSize)
            "\NUL"
            cmd
    LBS.fromStrict <$>
      (BS.packCString =<<
       [CU.exp| const char* {
               Z3_eval_smtlib2_string($fptr-ptr:(Z3_context ctx), $bs-ptr:cmd')
               }|])

-- | Release the resources associated with a Z3 instance.
close :: Handle -> IO ()
close = finalizeForeignPtr . context

-- | Create a Z3 instance, use it to run a computation and release its resources.
with :: (Handle -> IO a) -> IO a
with = bracket new close

