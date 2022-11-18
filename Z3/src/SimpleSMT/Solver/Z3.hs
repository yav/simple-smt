{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module SimpleSMT.Solver.Z3
  ( Z3
  , toBackend
  , newZ3Instance
  , freeZ3Instance
  ) where

import SimpleSMT.Solver (Backend(..))
import SimpleSMT.SExpr (SExpr, parseSExpr)

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.IORef (newIORef, modifyIORef)
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

data Z3 = Z3 { context :: ForeignPtr LogicalContext }

newZ3Instance :: IO Z3
newZ3Instance = do
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

toBackend :: Z3 -> IO Backend
toBackend z3 = do
  resp <- newIORef mempty
  return $
    flip Backend resp $ \cmd -> do
      let ctx = context z3
      -- Z3 requires null-terminated cstrings
      -- appending the null character performs a memcpy so is inefficient
      -- TODO a better solution would be to do this on the bytestring-build before it
      -- is evaluated to a lazy bytestring
      let cmd' = LBS.toStrict $ cmd `LBS.snoc` '\NUL'
      result <- BS.packCString =<<
               [CU.exp| const char* {
                   Z3_eval_smtlib2_string($fptr-ptr:(Z3_context ctx), $bs-ptr:cmd')
                   }|]
      modifyIORef resp (<> LBS.fromStrict result)

freeZ3Instance :: Z3 -> IO ()
freeZ3Instance = finalizeForeignPtr . context
