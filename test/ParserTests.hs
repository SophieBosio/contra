module ParserTests where

import Syntax
import Parser

import Test.Tasty
import Test.Tasty.HUnit
import Data.Either           (isLeft)
import Text.Parsec           (eof)
import Control.Monad         (void)


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
     testParseValuesOK
  ++ testParseValuesError
  ++ testParsePatternsOK
  ++ testParsePatternsError
  ++ testParseTermsOK
  ++ testParseTermsError

programTests :: TestTree
programTests =
  testGroup "Program parser tests: "
  []
  

-- Abbreviations
testSimpleOK :: (Eq a, Show a) => Parser a -> String -> a
                  -> Assertion
testSimpleOK p str expected =
  assertEqual ("Should parse: " ++ show str)
    (Right expected) (parseString p str)

testSimpleError :: (Eq a, Show a) => Parser a -> String -> Assertion
testSimpleError p str =
  assertBool ("*Should not parse: " ++ show str) $
    isLeft (parseString p str)

typelessTestOK :: (Functor f, Eq (f ()), Show (f ())) =>
                  Parser (f a) -> String -> f () -> Assertion
typelessTestOK p str expected =
  assertEqual ("Should parse: " ++ show str)
    (Right expected) (void <$> parseString p str)

typelessTestError :: (Functor f, Eq (f ()), Show (f ())) =>
                     Parser (f a) -> String -> Assertion
typelessTestError p str =
  assertBool ("*Should not parse: " ++ show str) $
    isLeft (void <$> parseString p str)


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
  , ("MyADT",       ADT "MyADT")
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
  , ("C",                  ADT "C")
  , ("Boolean -> Integer", Boolean' :->: Integer')
  , ("(Integer -> Boolean) -> Unit",
      (Integer' :->: Boolean') :->: Unit')
  , ("Integer -> (Boolean -> Unit)",
      Integer' :->: (Boolean' :->: Unit'))
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
testParseValuesOK :: [TestTree]
testParseValuesOK =
  map (\(s, e) -> testCase ("Parsing value '" ++ s ++ "'") $
                  typelessTestOK value s e)
  [ ("0",     Number 0    ())
  , ("-1",    Number (-1) ())
  , ("53",    Number 53   ())
  , ("True",  Boolean True ())
  , ("False", Boolean False ())
  , ("Unit",  Unit ())
  , ("(Unit)", Unit ())
  , ("Ctr",   VConstructor "Ctr" [] ())
  , ("(Ctr True 5)", VConstructor "Ctr" [Boolean True (), Number 5 ()] ())
  , ("Ctr 3 False",  VConstructor "Ctr" [Number 3 (), Boolean False ()] ())
  ]

testParseValuesError :: [TestTree]
testParseValuesError =
  map (\s -> testCase ("*Illegal value '" ++ s ++ "'") $
             typelessTestError value s)
  [ "false"
  , "true"
  , "unit"
  , "*ctr"
  ]

testParsePatternsOK :: [TestTree]
testParsePatternsOK =
  map (\(s, e) -> testCase ("Parsing pattern '" ++ s ++ "'") $
                  typelessTestOK pattern' s e)
  [ ("0",       Value (Number 0    ()))
  , ("-1",      Value (Number (-1) ()))
  , ("53",      Value (Number 53   ()))
  , ("True",    Value (Boolean True ()))
  , ("False",   Value (Boolean False ()))
  , ("Unit",    Value (Unit ()))
  , ("(False)", Value (Boolean False ()))
  ]

testParsePatternsError :: [TestTree]
testParsePatternsError =
  map (\s -> testCase ("*Illegal pattern '" ++ s ++ "'") $
             typelessTestError pattern' s)
  [ ""
  , "=false"
  , "*ctr"
  ]


testParseTermsOK :: [TestTree]
testParseTermsOK =
  map (\(s, e) -> testCase ("Parsing term '" ++ s ++ "'") $
                  typelessTestOK term s e)
  [
    ("0",  Pattern (Value (Number 0    ())))
  , ("-1", Pattern (Value (Number (-1) ())))
  , ("53", Pattern (Value (Number 53   ())))
  , ("3 + 5", Plus (Pattern (Value (Number 3 ()))) (Pattern (Value (Number 5 ()))) ())
  , ("5 - 3", Minus (Pattern (Value (Number 5 ()))) (Pattern (Value (Number 3 ()))) ())
  , ("3 < 5", Lt (Pattern (Value (Number 3 ()))) (Pattern (Value (Number 5 ()))) ())
  , ("5 > 3", Gt (Pattern (Value (Number 5 ()))) (Pattern (Value (Number 3 ()))) ())
  , ("(5 > 3)", Gt (Pattern (Value (Number 5 ()))) (Pattern (Value (Number 3 ()))) ())
  , ("2 == 2", Equal (Pattern (Value (Number 2 ()))) (Pattern (Value (Number 2 ()))) ())
  , ("(2 == 2)", Equal (Pattern (Value (Number 2 ()))) (Pattern (Value (Number 2 ()))) ())
  , ("not (3 == 5)", Not (Equal (Pattern (Value (Number 3 ()))) (Pattern (Value (Number 5 ()))) ()) ())
  , ("not (5 > 3)", Not (Gt (Pattern (Value (Number 5 ()))) (Pattern (Value (Number 3 ()))) ()) ())
  , ("3 5", Application (Pattern (Value (Number 3 ()))) (Pattern (Value (Number 5 ()))) ())
  , ("f x", Application (Pattern (Variable "f" ())) (Pattern (Variable "x" ())) ())
  , ("\\x -> \\f -> \\y -> f x y"
    , (Lambda "x"
         (Lambda "f"
            (Lambda "y"
               (Application
                  (Application
                   (Pattern (Variable "f" ()))
                    (Pattern (Variable "x" ())) ())
                (Pattern (Variable "y" ())) ()) ()) ()) ()))
    --let expressions, term constructors
  , ("case True of "       ++
     "| True  -> 5 " ++
     "| False -> 3 "
    ,  Case (Pattern (Value (Boolean True ())))
            [ (Value (Boolean True ()), Pattern (Value (Number 5 ())))
            , (Value (Boolean False ()), Pattern (Value (Number 3 ()))) ] ())
  , ("case x of "       ++
     "| 5     -> True " ++
     "| False -> False "
    ,  Case (Pattern (Variable "x" ()))
            [ (Value (Number 5 ()), Pattern (Value (Boolean True ())))
            , (Value (Boolean False ()), Pattern (Value (Boolean False ()))) ] ())
  , ("if True then 5 else 3"
    , Case (Pattern (Value (Number 3 ())))
           [ (Value (Boolean True ()),  Pattern (Value (Number 5 ())))
           , (Value (Boolean False ()), Pattern (Value (Number 3 ())))] ())
  -- , ("", )
  -- , ("", )
  ]


testParseTermsError :: [TestTree]
testParseTermsError =
  map (\s -> testCase ("*Illegal term '" ++ s ++ "'") $
             typelessTestError term s)
  [ ""
  , "=false"
  , "*ctr"
  ]


-- Parse whole programs
-- TODO Write example programs to parse
