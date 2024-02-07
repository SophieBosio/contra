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
  let ti = normalise p t in
  let pp = partiallyEvaluate p in
  let tip = normalise pp tip in
    assertBool "Should have evaluated to same term" (ti == tip)

evaluateToDifferentTerm :: (Show a, Eq a) => Program a -> Term a -> Assertion
evaluateToDifferentTerm p t =
  let ti = normalise p t in
  let pp = partiallyEvaluate p in
  let tip = normalise pp tip in
    assertBool "Should *not* have evaluated to same term" (ti /= tip)

-- Simple terms
emptyProgram :: Program Type
emptyProgram = End

-- TODO! Uh-oh, infinite loop...
simpleTerms =
  map (\t -> testCase
             ("Interpreting and partially evaluating term  '" ++ show t ++ "'")
             (evaluateToSameTerm emptyProgram t))
  [ Pattern (Unit Unit')
  , Pattern (Number 3 Integer')
  , Pattern (Boolean False Boolean')
  , Pattern (Constructor "x" [Number 5 Integer'] (ADT "C" [Integer']))
  ]
  

-- Variables
variables =
  map (\t -> testCase
             ("Interpreting and partially evaluating term  '" ++ show t ++ "'")
             (evaluateToSameTerm emptyProgram t))
  [ Pattern (Variable "x" Unit')
  , Pattern (Variable "x" Integer')
  , Pattern (Variable "x" Boolean')
  , Pattern (Variable "x" (Integer' :*:  Boolean'))
  , Pattern (Variable "x" (Boolean' :->: Boolean'))
  ]
