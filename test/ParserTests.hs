module ParserTests where

import Core.Syntax
import Core.Parser
  ( Parser
  , report
  , parseString
  , parseProgram
  , number
  , boolean
  , simpleType
  , type'
  , value
  , pattern'
  , term
  , program
  , reservedKeywords
  , flatten
  )

import Test.Tasty
import Test.Tasty.HUnit
import Text.Parsec           (eof, runParser)
import Data.Either           (isLeft)
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
  testGroup "Program parser tests: " $
       testParsePrograms
    ++ testParseErrorsPrograms
    ++ testFlattenProgram
  

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
  , ("Integer -> Integer -> Integer",
      Integer' :->: (Integer' :->: Integer'))
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
  [ ("0",        Value (Number 0    ()))
  , ("-1",       Value (Number (-1) ()))
  , ("53",       Value (Number 53   ()))
  , ("True",     Value (Boolean True ()))
  , ("False",    Value (Boolean False ()))
  , ("Unit",     Value (Unit ()))
  , ("(False)",  Value (Boolean False ()))
  , ("x",        Variable "x" ())
  , ("myVar1",   Variable "myVar1" ())
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
  , ("5 + (3 + 1)", Plus (Pattern (Value (Number 5 ())))
                      (Plus (Pattern (Value (Number 3 ())))
                            (Pattern (Value (Number 1 ())))
                      ())
                    ())
  , ("3 5", Application (Pattern (Value (Number 3 ()))) (Pattern (Value (Number 5 ()))) ())
  , ("f x", Application (Pattern (Variable "f" ())) (Pattern (Variable "x" ())) ())
  , ("let x = 3 in x + 5",
     Let (Variable "x" ()) (Pattern (Value (Number 3 ())))
             (Plus (Pattern (Variable "x" ()))
                   (Pattern (Value (Number 5 ())))
              ())
       ())
  , ("\\x -> \\f -> \\y -> f x y", 
     Lambda (Variable "x" ())
      (Lambda (Variable "f" ())
        (Lambda (Variable "y" ())
          (Application
            (Application
              (Pattern (Variable "f" ())) (Pattern (Variable "x" ())) ())
            (Pattern (Variable "y" ())) ())
          ())
        ())
      ())
  , ("case True of "       ++
     "; True  -> 5 " ++
     "; False -> 3 "
    ,  Case (Pattern (Value (Boolean True ())))
            [ (Value (Boolean True ()), Pattern (Value (Number 5 ())))
            , (Value (Boolean False ()), Pattern (Value (Number 3 ()))) ] ())
  , ("case x of "       ++
     "; 5     -> True " ++
     "; False -> False "
    ,  Case (Pattern (Variable "x" ()))
            [ (Value (Number 5 ()), Pattern (Value (Boolean True ())))
            , (Value (Boolean False ()), Pattern (Value (Boolean False ()))) ] ())
  , ("case 5 of "       ++
     "; 3 -> False " ++
     "; 5 -> True "
    ,  Case (Pattern (Value (Number 5 ())))
            [ (Value (Number 3 ()), Pattern (Value (Boolean False ())))
            , (Value (Number 5 ()), Pattern (Value (Boolean True ()))) ] ())
  , ("if True then 5 else 3"
    , Case (Pattern (Value (Boolean True ())))
           [ (Value (Boolean True  ()),  Pattern (Value (Number 5 ())))
           , (Value (Boolean False ()), Pattern (Value (Number 3 ())))] ())
  , ("if (3 < 5) then 10 else (10 - 5)"
    , Case (Lt (Pattern (Value (Number 3 ())))
               (Pattern (Value (Number 5 ()))) ())
           [ (Value (Boolean True  ()), Pattern (Value (Number 10 ())))
           , (Value (Boolean False ()), Minus (Pattern (Value (Number 10 ())))
                                              (Pattern (Value (Number 5  ())))
                                        ())
           ] ())
  , ("Ctr", Pattern $ Value $ VConstructor "Ctr" [] ())
  , ("Ctr {5}", Pattern $ Value $ VConstructor "Ctr" [Number 5 ()] ())
  , ("Ctr {True}", Pattern $ Value $ VConstructor "Ctr" [Boolean True ()] ())
  , ("Ctr {x}", Pattern $ PConstructor "Ctr" [Variable "x" ()] ())
  , ("Ctr {x, False}", Pattern $ PConstructor "Ctr"
      [ Variable "x" ()
      , Value (Boolean False ())
      ] ())
  , ("Ctr {x, (5 + 3), True}"
    , TConstructor "Ctr"
        [ Pattern (Variable "x" ())
        , Plus (Pattern (Value (Number 5 ())))
               (Pattern (Value (Number 3 ()))) ()
        , Pattern (Value (Boolean True ()))
        ] ())
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
testParsePrograms :: [TestTree]
testParsePrograms =
  map (\(file, p) -> testCase ("Parsing program '" ++ file ++ "'") $
      do src <- readFile file
         let ast = void <$> runParser program () file src
         assertEqual "" (return p) ast)
  [ ("examples/test/basicStatements.con",
     Data "MyADT" [Constructor "YES" [], Constructor "NO" []] $
     Signature "id" (ADT "MyADT" :->: ADT "MyADT") $
     Function "id" (Lambda (Variable "x" ()) (Pattern (Variable "x" ())) ()) $
     Signature "propId" (ADT "MyADT" :->: Boolean') $
     Property "propId" (Lambda (Variable "x" ())
                        (Equal (Pattern (Variable "x" ()))
                               (Pattern (Variable "x" ())) ()) ())
     End)
  , ("examples/test/simpleAdd.con",
     Signature "simpleAdd" (Integer' :->: (Integer' :->: Integer')) $
     Function "simpleAdd"
      (Lambda (Variable "x" ())
        (Lambda (Variable "y" ())
          (Plus
            (Pattern (Variable "x" ()))
            (Pattern (Variable "y" ()))
            ())
          ())
        ()) $
     Signature "double" (Integer' :->: Integer') $
     Function "double"
       (Lambda (Variable "x" ())
         (Application
          (Application
            (Pattern (Variable "simpleAdd" ()))
            (Pattern (Variable "x" ()))
           ())
          (Pattern (Variable "x" ()))
         ())
        ()) $
     Signature "isFive" (Integer' :->: Boolean') $
     Function "isFive" (Lambda (Variable "x" ())
                         (Equal (Pattern (Variable "x" ()))
                                (Pattern (Value (Number 5 ()))) ())
                         ()) $
     Signature "sillyIsFive" (Integer' :->: Boolean') $
     Function "sillyIsFive"
      (Lambda (Variable "x" ())
        (Case (Equal (Pattern (Variable "x" ()))
                     (Pattern (Value (Number 5 ()))) ())
          [ (Value (Boolean True  ()), Pattern (Value (Boolean True ())))
          , (Value (Boolean False ()), Pattern (Value (Boolean False ())))
          ]
         ())
        ()) $
     Signature "fiveNotThree" (Integer' :->: Boolean') $
     Function "fiveNotThree"
       (Lambda (Variable "x" ())
         (Case (Pattern (Variable "x" ()))
           [ (Value (Number 5 ())
             , Pattern (Value (Boolean True ())))
           , (Value (Number 3 ())
             , Pattern (Value (Boolean False ())))
           ] ())
         ()) $
     Signature "greaterThanFive" (Integer' :->: Boolean') $
     Function "greaterThanFive"
       (Lambda (Variable "x" ())
         (Gt (Pattern (Variable "x" ())) (Pattern (Value (Number 5 ()))) ())
        ()) $
     Signature "addFive" (Integer' :->: Integer') $
     Function "addFive"
       (Lambda (Variable "x" ())
        (Application
          (Application 
            (Pattern (Variable "simpleAdd" ()))
            (Pattern (Value (Number 5 ())))
          ())
          (Pattern (Variable "x" ()))
         ())
       ()) $
     Signature "trivialProp" (Integer' :->: Boolean') $
     Property "trivialProp"
       (Lambda (Variable "x" ())
         (Application
           (Pattern (Variable "isFive" ()))
           (Pattern (Variable "x" ()))
           ())
         ()) $
     Signature "sumEqualsFive" (Integer' :->: (Integer' :->: Boolean')) $
     Property "sumEqualsFive"
       (Lambda (Variable "x" ())
        (Lambda (Variable "y" ())
         (Application (Pattern (Variable "isFive" ()))
          (Application
           (Application (Pattern (Variable "simpleAdd" ()))
                        (Pattern (Variable "x" ())) ())
           (Pattern (Variable "y" ()))
           ())
          ())
         ())
        ()) $
     Signature "preconditionProp" (Integer' :->: Boolean') $
     Property "preconditionProp"
      (Lambda (Variable "x" ())
       (Case (Application (Pattern (Variable "greaterThanFive" ()))
                          (Pattern (Variable "x" ())) ())
         [ (Value (Boolean True  ()), Application
                                      (Pattern (Variable "greaterThanFive" ()))
                                       (Application
                                         (Application (Pattern (Variable "simpleAdd" ()))
                                                      (Pattern (Variable "x" ()))
                                           ())
                                         (Pattern (Variable "x" ())) ())
                                      ())
         , (Value (Boolean False ()), Pattern (Value (Boolean True ())))
         ]
        ())
      ())
     End)
  ]

testFlattenProgram :: [TestTree]
testFlattenProgram =
  -- Unflattened
  map (\(file, p) -> testCase ("Parsing unflattened program '" ++ file ++ "'") $
      do src <- readFile file
         let ast = void <$> runParser program () file src
         assertEqual "" (return p) ast)
  [ ("examples/test/multipleFunctionDefinitions.con",
     Signature "f" (Integer' :->: (Integer' :->: (Integer' :->: Integer'))) $
     Function "f"
      (Lambda (Value (Number 5 ()))
       (Lambda (Variable "y" ())
        (Lambda (Variable "z" ())
          (Plus
            (Plus
              (Pattern (Value (Number 5 ())))
              (Pattern (Variable "y" ()))
             ())
            (Pattern (Variable "z" ()))
           ())
         ())
        ())
       ()) $
     Function "f"
      (Lambda (Variable "x" ())
       (Lambda (Value (Number 4 ()))
        (Lambda (Variable "z" ())
          (Minus
            (Minus
              (Pattern (Variable "x" ()))
              (Pattern (Value (Number 4 ())))
             ())
            (Pattern (Variable "z" ()))
           ())
         ())
        ())
       ()) $
     Function "f"
      (Lambda (Variable "x" ())
       (Lambda (Variable "y" ())
       (Lambda (Value (Number 3 ()))
          (Minus
            (Plus
              (Pattern (Variable "x" ()))
              (Pattern (Variable "y" ()))
             ())
            (Pattern (Value (Number 3 ())))
           ())
         ())
        ())
       ()) $
     Function "f"
      (Lambda (Variable "x" ())
       (Lambda (Variable "y" ())
        (Lambda (Variable "z" ())
          (Plus
            (Plus
              (Pattern (Variable "x" ()))
              (Pattern (Variable "x" ()))
             ())
            (Plus
              (Pattern (Variable "y" ()))
              (Pattern (Variable "z" ()))
             ())
           ())
         ())
        ())
       ()) $
     Signature "and" (Boolean' :->: (Boolean' :->: Boolean')) $
     Function "and"
      (Lambda (Value (Boolean True ()))
       (Lambda (Value (Boolean True ()))
         (Pattern (Value (Boolean True ())))
        ())
       ()) $
     Function "and"
      (Lambda (Value (Boolean True ()))
       (Lambda (Value (Boolean False ()))
         (Pattern (Value (Boolean False ())))
        ())
       ()) $
     Function "and"
      (Lambda (Value (Boolean False ()))
       (Lambda (Value (Boolean True ()))
         (Pattern (Value (Boolean False ())))
        ())
       ()) $
     Function "and"
      (Lambda (Value (Boolean False ()))
       (Lambda (Value (Boolean False ()))
         (Pattern (Value (Boolean False ())))
        ())
       ())
     End)
  ]
  ++
  -- Flattened
  map (\(file, p) -> testCase ("Parsing flattened program '" ++ file ++ "'") $
       do src <- readFile file
          let ast = void <$> runParser program () file src
          let flat = flatten <$> ast
          assertEqual "" (return p) flat)
  [ ("examples/test/multipleFunctionDefinitions.con",
     Signature "f" (Integer' :->: (Integer' :->: (Integer' :->: Integer'))) $
     Signature "and" (Boolean' :->: (Boolean' :->: Boolean')) $
     Function "and"
      (Lambda (Variable "*a" ())
       (Lambda (Variable "*b" ())
        (Case (Pattern (List [ Variable "*a" ()
                             , Variable "*b" ()
                             ] ()))
         [ (List [Value (Boolean True ()), Value (Boolean True ())] (),
           Pattern (Value (Boolean True ())))
         , (List [Value (Boolean True ()), Value (Boolean False ())] (),
           Pattern (Value (Boolean False ())))
         , (List [Value (Boolean False ()), Value (Boolean True ())] (),
           Pattern (Value (Boolean False ())))
         , (List [Value (Boolean False ()), Value (Boolean False ())] (),
           Pattern (Value (Boolean False ())))
         ]
        ())
       ())
      ()) $
     Function "f"
      (Lambda (Variable "*a" ())
       (Lambda (Variable "*b" ())
        (Lambda (Variable "*c" ())
          (Case (Pattern (List [ Variable "*a" ()
                               , Variable "*b" ()
                               , Variable "*c" ()
                               ] ()))
            [ (List [Value (Number 5 ()), Variable "y" (), Variable "z" ()] (),
               Plus
               (Plus
                (Pattern (Value (Number 5 ())))
                (Pattern (Variable "y" ()))
                ())
               (Pattern (Variable "z" ()))
               ())
            , (List [Variable "x" (), Value (Number 4 ()), Variable "z" ()] (),
               Minus
               (Minus
                (Pattern (Variable "x" ()))
                (Pattern (Value (Number 4 ())))
                ())
               (Pattern (Variable "z" ()))
               ())
            , (List [Variable "x" (), Variable "y" (), Value (Number 3 ())] (),
               Minus
               (Plus
                (Pattern (Variable "x" ()))
                (Pattern (Variable "y" ()))
                ())
               (Pattern (Value (Number 3 ())))
               ())
            , (List [Variable "x" (), Variable "y" (), Variable "z" ()] (),
               Plus
               (Plus
                (Pattern (Variable "x" ()))
                (Pattern (Variable "x" ()))
                ())
               (Plus
                (Pattern (Variable "y" ()))
                (Pattern (Variable "z" ()))
                ())
               ())
            ]
          ())
         ())
        ())
       ())
     End)
  ]

testParseErrorsPrograms :: [TestTree]
testParseErrorsPrograms =
  map (\(file, err) -> testCase ("Parsing erronous program '" ++ file ++ "'") $
      do result <- parseProgram file
         case result of
           Right _ -> assertFailure "Should have produced a parsing error."
           Left es -> assertEqual "" err (report es))
  [ ("examples/errors/multipleSignatures.con"
    , "Multiple type signatures declared for function/property with name 'clone'\n")
  , ("examples/errors/multipleADTs.con"
    , "Multiple ADTs declared with name 'MyADT'\n")
  , ("examples/errors/multipleCtrs.con"
    , "Multiple constructors declared with name 'C'\n")
  , ("examples/errors/multipleProperties.con"
    , "Multiple properties declared with name 'clone'\n beginning at \n\"examples/errors/multipleProperties.con\" (line 1, column 7)\n and ending at\n\"examples/errors/multipleProperties.con\" (line 1, column 9)\n")
  ]
