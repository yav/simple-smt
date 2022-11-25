import qualified SimpleSMT.Tests.SExpr as SExpr

import Test.Tasty


main :: IO ()
main = do
  defaultMain $ testGroup "Tests" $ [ SExpr.tests ] 
