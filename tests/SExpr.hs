{-# LANGUAGE OverloadedStrings #-}
module SExpr (tests) where

import qualified SimpleSMT.SExpr as SExpr
import qualified Sources as Src
  
import Control.Monad (zipWithM_)
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.List (unfoldr)
import Data.List.Extra (trim)
import Data.Maybe (isJust)
import Test.Tasty
import Test.Tasty.HUnit
  
tests :: TestTree
tests =
  testGroup
    "SExpr"
    [ testGroup "Parsing" $ do
        source <- Src.sources
        return $
          testCase (Src.name source) $ do
            let expecteds = Src.parsed source
                gots = unfoldr SExpr.readSExpr $ Src.content source
            zipWithM_
              (\expected got ->
                 assertBool
                   ("  parsed:   '" ++
                    show got ++ "\n  expected: '" ++ show expected) $
                 expected == got)
              expecteds
              gots
            let numExpected = length expecteds
                numGot = length gots
            assertBool
              ("parsed " ++
               show numGot ++ " expressions but expected " ++ show numExpected) $
              numExpected == numGot
    ]
