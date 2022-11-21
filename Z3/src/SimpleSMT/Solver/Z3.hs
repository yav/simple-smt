{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module SimpleSMT.Solver.Z3
  ( Z3(..)
  , new
  , free
  , with
  , toBackend
  ) where

import qualified SimpleSMT.Solver as Solver

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

data Z3 = Z3
    { context :: ForeignPtr LogicalContext
    -- ^ A black-box representing the internal state of the solver.
    }

-- | Create a new solver instance.
new :: IO Z3
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
  return $ Z3 ctx

-- | Release the resources associated with a Z3 instance.
free :: Z3 -> IO ()
free = finalizeForeignPtr . context

-- | Create a Z3 instance, use it to run a computation and release its resources.
with :: (Z3 -> IO a) -> IO a
with todo = do
  z3 <- new
  result <- todo z3
  free z3
  return result

-- | Create a solver backend out of a Z3 instance.
toBackend :: Z3 -> Solver.Backend
toBackend z3 =
  Solver.Backend $ \cmd -> do
    let ctx = context z3
    -- Z3 requires null-terminated cstrings
    -- appending the null character performs a memcpy so is inefficient
    -- TODO a better solution would be to do this on the bytestring-build before it
    -- is evaluated to a lazy bytestring
    let cmd' = LBS.toStrict $ cmd `LBS.snoc` '\NUL'
    LBS.fromStrict <$> (BS.packCString =<<
      [CU.exp| const char* {
               Z3_eval_smtlib2_string($fptr-ptr:(Z3_context ctx), $bs-ptr:cmd')
               }|])
