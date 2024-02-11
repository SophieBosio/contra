module PartialEvaluatorTests where

import Syntax
import Interpreter
import PartialEvaluator

import Test.Tasty
import Test.Tasty.HUnit

partialEvaluatorTests :: TestTree
partialEvaluatorTests =
  testGroup "Interpreting and partially evaluating term yields same result: "
    simpleTerms


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
  , Pattern (PConstructor "x" [Value (Number 5 Integer')] (ADT "X" [Integer']))
  , Pattern (Value (VConstructor "y" [VConstructor "z" [Boolean True Boolean', Number 3 Integer'] (ADT "Z" [Boolean', Integer'])] (ADT "Y" [ADT "Z" [Boolean', Integer']])))
  ]


-- Variables
variables :: [TestTree]
variables =
  map (\t -> testCase
             ("Interpreting and partially evaluating term  '" ++ show t ++ "'")
             (evaluateToSameTerm emptyProgram t))
  [ Pattern (Variable "x" Unit')
  , Pattern (Variable "x" Integer')
  , Pattern (Variable "x" Boolean')
  , Pattern (Variable "x" (Boolean' :->: Boolean'))
  ]
