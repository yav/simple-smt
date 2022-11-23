import qualified SExpr as SExpr

import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.List (isSuffixOf)
import System.Directory (listDirectory)
import Test.Tasty

main :: IO ()
main = do
  defaultMain $ testGroup "Tests" $ [ SExpr.tests ] 
