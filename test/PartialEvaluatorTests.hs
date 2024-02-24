module PartialEvaluatorTests where

import Syntax
import Interpreter
import PartialEvaluator
import Parser

import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad (void)


-- Export
partialEvaluatorTests :: TestTree
partialEvaluatorTests =
  testGroup "Interpreting and partially evaluating term yields same result: " $
       simpleTerms
    ++ testPartialEvalPrograms


-- Helpers
evaluateToSameTerm :: (Show a, Eq a) => Program a -> Term a -> Assertion
evaluateToSameTerm p t =
  let ti       = normalise         p  t  in
  let (tp, pp) = partiallyEvaluate p  t  in
  let tip      = normalise         pp tp in
    assertBool "Should have evaluated to same term" (ti == tip)

evaluateToDifferentTerm :: (Show a, Eq a) => Program a -> Term a -> Assertion
evaluateToDifferentTerm p t =
  let ti       = normalise         p  t  in
  let (tp, pp) = partiallyEvaluate p  t  in
  let tip      = normalise         pp tp in
    assertBool "Should *not* have evaluated to same term" (ti /= tip)

parseAndStrip :: String -> IO (Program ())
parseAndStrip filePath =
  do src    <- readFile filePath
     result <- parseProgram src
     case result of
       Left  _ -> error $ "Parsing error in program " ++ filePath
       Right p -> return $ void p

programTestOK :: (Show a, Eq a) => (Program a, Term a, Term a) -> Assertion
programTestOK (p, t, e) =
  assertEqual ""
    e (fst $ partiallyEvaluate p t)



-- Simple terms
emptyProgram :: Program Type
emptyProgram = End

simpleTerms :: [TestTree]
simpleTerms =
  map (\t -> testCase
             ("Interpreting and partially evaluating term  '" ++ show t ++ "'")
             (evaluateToSameTerm emptyProgram t))
  [ Pattern (Value (Unit Unit'))
  , Pattern (Value (Number 3 Integer'))
  , Pattern (Value (Boolean False Boolean'))
  , Pattern (PConstructor "x" [Value (Number 5 Integer')] (ADT "X"))
  , Pattern (Value (VConstructor "y"
                     [VConstructor "z"
                       [Boolean True Boolean', Number 3 Integer']
                       (ADT "Z")]
                     (ADT "Y")))
  ]


-- Programs
-- (test programs at the bottom)
testPartialEvalPrograms :: [TestTree]
testPartialEvalPrograms =
  map (\(p, t, e) -> let t' = (Unit' <$ t) in
                     let e' = (Unit' <$ e) in
                     let p' = (Unit' <$ p)
                     in  testCase
                         ("Checking partial evaluation for term '" ++ show t' ++ "'") $
                         programTestOK (p', t', e'))
  [ (p1, t1, e1)
  ]



p1 :: Program ()
p1 =
  Signature "simpleAdd" (Integer' :->: (Integer' :->: Integer')) $
     Function "simpleAdd"
      (Lambda "x"
        (Lambda "y"
          (Plus
            (Pattern (Variable "x" ()))
            (Pattern (Variable "y" ()))
            ())
          ())
        ()) $
     Signature "addFive" (Integer' :->: Integer') $
     Function "addFive"
       (Lambda "x"
        (Application
          (Application
            (Pattern (Variable "simpleAdd" ()))
            (Pattern (Value (Number 5 ())))
          ())
          (Pattern (Variable "x" ()))
         ())
       ())
     End

t1 :: Term ()
t1 =
  Lambda "x"
    (Application
      (Application
        (Pattern (Variable "simpleAdd" ()))
        (Pattern (Value (Number 5 ())))
      ())
      (Pattern (Variable "x" ()))
     ())
   ()

e1 :: Term ()
e1 =
  Lambda "x"
    (Application
      (Lambda "y"
       (Plus
         (Pattern (Value (Number 5 ())))
         (Pattern (Variable "y" ()))
         ())
       ())
      (Pattern (Variable "x" ()))
    ())
  ()
