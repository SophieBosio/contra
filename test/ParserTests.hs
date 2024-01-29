module ParserTests where

import Syntax
import Parser

import Data.Either (isLeft)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC


utilityParsers :: TestTree
utilityParsers =
  testGroup "Utility parser tests: " $
     testParseNumbersOK
  ++ testParseNumbersError
  ++ testParseBoolsOK
  ++ testParseBoolsError

patternParser :: TestTree
patternParser =
  testGroup "Pattern parser tests: " $
  []

termParser :: TestTree
termParser =
  testGroup "Term parser tests: " $
  []

typeParser :: TestTree
typeParser =
  testGroup "Type parser tests: " $
     testParseSimpleTypesOK
  ++ testParseSimpleTypesError
  ++ testParseRegularTypesOK
  ++ testParseRegularTypesError
  ++ testParseTypesOK
  ++ testParseTypesError

programTests :: TestTree
programTests =
  testGroup "Pattern parser tests: " $
  []
  

-- Abbreviations
testSimpleOK :: (Eq a, Show a) => Parser a -> String -> a
                  -> Assertion
testSimpleOK p str expected =
  assertEqual ("Should parse: " ++ show str)
    (Right expected) (parseString p str)

testSimpleError p str =
  assertBool ("*Should not parse: " ++ show str) $
    isLeft (parseString p str)


-- Utility parsers
testParseNumbersOK :: [TestTree]
testParseNumbersOK =
  map (\(s, e) -> testCase ("'" ++ s ++ "' is an int") $
                  testSimpleOK number s e)
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
testParseNumbersError =
  map (\s -> testCase ("* '" ++ s ++ "' is not a valid int") $
             testSimpleError number s)
  [ "a1"
  , "a1a"
  , ".1"
  , ",1"
  , ""
  ]

testParseBoolsOK :: [TestTree]
testParseBoolsOK =
  map (\(s, e) -> testCase ("'" ++ s ++ "' is a boolean") $
                  testSimpleOK boolean s e)
  [ ("True",  True)
  , ("False", False)
  ]

testParseBoolsError :: [TestTree]
testParseBoolsError =
  map (\s -> testCase ("* '" ++ s ++ "' is lowercase or reserved (illegal)") $
             testSimpleError boolean s)
  ([ "true"
   , "false"
   ]
  ++ reservedKeywords)


-- Parse patterns
testParsePatterns :: [TestTree]
testParsePatterns = undefined


-- Parse terms
testParseTerms :: [TestTree]
testParseTerms = undefined


-- Parse types
testParseSimpleTypesOK :: [TestTree]
testParseSimpleTypesOK =
  map (\(s, e) -> testCase ("Parsing simple type '" ++ s ++ "'") $
                  testSimpleOK simpleType s e)
  [ ("0",           Variable' 0)
  , ("3",           Variable' 3)
  , ("321",         Variable' 321)
  , ("Unit",        Unit')
  , ("Integer",     Integer')
  , ("Boolean",     Boolean')
  , ("(Integer)",   Integer')
  , ("((Integer))", Integer')
  , ("C Integer",   ADT "C" [Integer'])
  , ("Ctr Ctr_ Boolean Integer",
      ADT "Ctr" [ADT "Ctr_" [Boolean', Integer']])
  ]

testParseSimpleTypesError :: [TestTree]
testParseSimpleTypesError =
  map (\s -> testCase ("* Illegal type '" ++ s ++ "'") $
             testSimpleError type' s)
  ("" : reservedKeywords)
  -- TODO

testParseRegularTypesOK :: [TestTree]
testParseRegularTypesOK =
  map (\(s, e) -> testCase ("Parsing regular type '" ++ s ++ "'") $
                  testSimpleOK regularType s e)
  [ ("(Integer, Integer)",         Integer' :*: Integer')
  , ("(Boolean, Unit)",            Boolean' :*: Unit')
  , ("(Integer, Boolean)",         Integer' :*: Boolean')
  , ("((Integer, Unit), Boolean)", (Integer' :*: Unit') :*: Boolean')
  , ("(Integer, (Unit, Boolean))", Integer' :*: (Unit' :*: Boolean'))
  , ("3",                          Variable' 3)
  , ("Unit",                       Unit')
  , ("Integer",                    Integer')
  , ("Boolean",                    Boolean')
  , ("(Integer)",                  Integer')
  ]

testParseRegularTypesError :: [TestTree]
testParseRegularTypesError =
  map (\s -> testCase ("* Illegal type '" ++ s ++ "'") $
             testSimpleError regularType s)
  [ "(Integer, Integer"
  , "(Integer, )"
  , ""
  ]
  

testParseTypesOK :: [TestTree]
testParseTypesOK =
  map (\(s, e) -> testCase ("Parsing type '" ++ s ++ "'") $
                  testSimpleOK type' s e)
  [ ("0",                  Variable' 0)
  , ("3",                  Variable' 3)
  , ("321",                Variable' 321)
  , ("Unit",               Unit')
  , ("Integer",            Integer')
  , ("Boolean",            Boolean')
  , ("(Unit)",             Unit')
  , ("(Unit, Unit)",       Unit' :*: Unit')
  , ("(Integer, Boolean)", Integer' :*: Boolean')
  , ("Boolean -> Integer", Boolean' :->: Integer')
  , ("C Integer",          ADT "C" [Integer'])
  , ("Ctr Ctr_ Boolean Integer",
      ADT "Ctr" [ADT "Ctr_" [Boolean', Integer']])
  ]
  

testParseTypesError :: [TestTree]
testParseTypesError =
  map (\s -> testCase ("* Illegal type '" ++ s ++ "'") $
             testSimpleError type' s)
  ("" : reservedKeywords)
  -- TODO


-- Parse whole programs
-- TODO! Write example programs to parse
