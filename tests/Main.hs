import qualified SimpleSMT.Tests.SExpr as SExpr
import qualified SimpleSMT.Tests.Solver as Solver

import Test.Tasty


main :: IO ()
main = do
  defaultMain $ testGroup "Tests" $ [ SExpr.tests, Solver.tests ]
