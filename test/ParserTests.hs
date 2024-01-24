module ParserTests where

import Syntax
import Parser

import Data.Either (isLeft)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

parserTests :: TestTree
parserTests =
  testGroup "Main parser tests: " $
     testParseNumbersOK
  ++ testParseNumbersError


-- Abbreviations
-- testError :: Show a => Parser a -> String -> TestTree
-- testError testName p s = testCase ("*" ++ testName) $
--   assertEqual

testSimpleOK :: (Eq a, Show a) => Parser a -> String -> a
                  -> Assertion
testSimpleOK p str expected =
  assertEqual ("Should parse: " ++ show str)
    (Right expected) (parseString p str)

testSimpleError p str =
  assertBool ("Should *not* parse: " ++ show str) $
    isLeft (parseString p str)


-- Parsing tests
testParseTerms :: [TestTree]
testParseTerms = undefined

testParsePatterns :: [TestTree]
testParsePatterns = undefined

testParseNumbersOK :: [TestTree]
testParseNumbersOK =
  map (\(s, e) -> testCase ("'" ++ show s ++ "' is an int") $ testSimpleOK number s e)
    [ ("0",         0)
    , ("2",         2)
    , ("-1",       -1)
    , ("000",       0)
    , ("02",        2)
    , ("-01",      -1)
    , ("38",       38)
    , ("1987",   1987)
    , ("-1987", -1987)
    ]

testParseNumbersError :: [TestTree]
testParseNumbersError = []
