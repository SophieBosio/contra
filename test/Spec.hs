import Test.Tasty

import InterpreterTests
-- import ParserTests
-- import TypeInferrerTests
-- import UnificationTests
-- import GeneratorsTests
-- import PartialEvaluationTests


timeoutSeconds :: Integer -> Timeout
timeoutSeconds = mkTimeout . (* 1000000)

main :: IO ()
main = defaultMain $ localOption (timeoutSeconds 10) tests

tests :: TestTree
tests =
  testGroup "Contra - Main Test Suite"
    [ testGroup "Interpreter: "
        [
          interpreterTests
        ]
    , testGroup "Parser: "
        [
        ]
    , testGroup "Type inferrer: "
        [
        ]
    , testGroup "Unification: "
        [
        ]
    , testGroup "Generators: "
        [
        ]
    , testGroup "Partial evaluation: "
        [
        ]
    ]
