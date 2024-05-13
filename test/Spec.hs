import Test.Tasty

import ParserTests
import PartialEvaluatorTests
import UnificationTests
import PropertyCheckerTests


timeoutSeconds :: Integer -> Timeout
timeoutSeconds = mkTimeout . (* 1000000)

main :: IO ()
main = defaultMain $ localOption (timeoutSeconds 10) tests

tests :: TestTree
tests =
  testGroup " ✱ Contra - Main Test Suite"
    [ testGroup "Parser: "
        [
          utilityParsers
        , typeParser
        , termParser
        , programTests
        ]
    , testGroup "Unification: "
        [
          substitutionTests
        ]
    , testGroup "Partial evaluator: "
        [
          partialEvaluatorTests
        ]
    , testGroup "Property checker: "
        [
          simple
        , programs
        ]
    ]
