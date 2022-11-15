{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module SimpleSMT.Solver.Z3 (Z3) where

import SimpleSMT.Solver (Backend)
import SimpleSMT.SExpr (parseSExpr)

import qualified Data.ByteString.Char8 as BS
import qualified Data.Map as M
import Foreign.Ptr (Ptr)
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

instance Backend Z3 where
  send z3 cmd = do
    let ctx = context z3
    let cmd' = BS.toStrict cmd
    resp <- [CU.exp| const char* {
                   Z3_eval_smtlib2_string($fptr-ptr:(Z3_context ctx), $bs-ptr:cmd)
                   } |]
      >>= BS.packCString
    case parseSExpr resp of
      Nothing -> do
        fail $ "Z3 failed with:\n" ++ BS.unpack resp
      Just (sexpr, _) -> do
        return sexpr

newZ3Instance :: IO (Solver Z3) 
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
  let solver = Solver (Z3 ctx)
  setOption solver ":print-success" "true"
  setOption solver ":produce-models" "true"
  return solver

freeZ3Instance :: Z3 -> IO ()
freeZ3Instance = finalizeForeignPtr . context


