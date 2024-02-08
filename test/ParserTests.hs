module ParserTests where

import Syntax
import Parser

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Data.Either (isLeft)
import Text.Parsec (eof)


utilityParsers :: TestTree
utilityParsers =
  testGroup "Utility parser tests: " $
     testParseNumbersOK
  ++ testParseNumbersError
  ++ testParseBoolsOK
  ++ testParseBoolsError

typeParser :: TestTree
typeParser =
  testGroup "Type parser tests: " $
     testParseSimpleTypesOK
  ++ testParseSimpleTypesError
  ++ testParseTypesOK
  ++ testParseTypesError

termParser :: TestTree
termParser =
  testGroup "Term parser tests: " $
  []

functionParser :: TestTree
functionParser =
  testGroup "Function parser tests: " $
  []

propertyParser :: TestTree
propertyParser =
  testGroup "Property parser tests: " $
  []

signatureParser :: TestTree
signatureParser =
  testGroup "Signature parser tests: " $
  []

adtParser :: TestTree
adtParser =
  testGroup "ADT parser tests: " $
  []

programTests :: TestTree
programTests =
  testGroup "Program parser tests: " $
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
  , ("MyADT",       ADT "MyADT" [])
  , ("C Integer",   ADT "C" [Integer'])
  , ("Ctr Ctr_ Boolean Integer",
      ADT "Ctr" [ADT "Ctr_" [Boolean', Integer']])
  ]

testParseSimpleTypesError :: [TestTree]
testParseSimpleTypesError =
  map (\s -> testCase ("* Illegal type '" ++ s ++ "'") $
             testSimpleError type' s)
  ("" : reservedKeywords)

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
  , ("Boolean -> Integer", Boolean' :->: Integer')
  , ("(Integer -> Boolean) -> Unit",
      (Integer' :->: Boolean') :->: Unit')
  , ("Integer -> (Boolean -> Unit)",
      Integer' :->: (Boolean' :->: Unit'))
  , ("C Integer",          ADT "C" [Integer'])
  , ("Ctr Ctr_ Boolean Integer",
      ADT "Ctr" [ADT "Ctr_" [Boolean', Integer']])
  ]
  

testParseTypesError :: [TestTree]
testParseTypesError =
  map (\s -> testCase ("* Illegal type '" ++ s ++ "'") $
             testSimpleError (type' >> eof) s) $
  ("" : reservedKeywords) ++
  [ "Integer ->"
  , "(Boolean, )"
  , "-> Boolean"
  , "(, Unit)"
  , "(,)"
  , "->"
  ]


-- Parse terms
testParseTerms :: [TestTree]
testParseTerms = undefined


-- Parse functions


-- Parse properties


-- Parse function signatures
-- testParseSignaturesOK :: [TestTree]
-- testParseSignaturesOK =
--   map (\(s, e) -> testCase ("Parsing function signature '" ++ s ++ "'") $
--                   testSimpleOK (signature' >> eof) s e)
--   [ ("add :: Integer -> Integer -> Integer",
--      Signature "add" ((Integer' :->: Integer') :->: Integer') End)
--   , ("addTuple :: (Integer, Integer) -> Integer", )
--   , ("addPedantic :: (Integer -> Integer) -> Integer", )
--   , ("constant :: Integer", )
--   , ("constant :: Boolean", )
--   , ("un :: Unit", )
--   , ("complex :: (Integer -> Integer) -> (Boolean -> Boolean)", )
--   , ("complex2 :: (Boolean -> Boolean) -> (Integer, Integer)", )
--   ]

-- testParseSignaturesError :: [TestTree]
-- testParseSignaturesError =
--   map (\s -> testCase ("* Illegal function signature '" ++ s ++ "'") $
--              testSimpleError signature' s)
--   []


-- Parse ADTs


-- Parse whole programs
-- TODO! Write example programs to parse
