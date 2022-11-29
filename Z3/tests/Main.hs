import SimpleSMT.Tests
import qualified SimpleSMT.Solver.Z3 as Z3

import Test.Tasty


main :: IO ()
main = do
  defaultMain $
    testGroup "Tests" $
    [ testBackend "Z3" validSources noLogging $ \todo ->
        Z3.with $ todo . Z3.toBackend
    ]
  where
    noLogging = const $ return ()
    validSources = filter (\source -> name source `notElem` ["assertions", "unsat cores", "terms"]) sources
