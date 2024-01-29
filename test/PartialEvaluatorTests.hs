module PartialEvaluatorTests where

import Syntax
import Interpreter
import PartialEvaluator

import Test.Tasty
import Test.Tasty.HUnit

partialEvaluatorTests :: TestTree
partialEvaluatorTests =
  testGroup "Interpreting a term and a partially evaluated term yields the same result: "
    [
    ]


evaluateToSameTerm :: (Show a, Eq a) => Program a -> Term a -> Bool
evaluateToSameTerm p t =
  let ti = normalise p t in
  let pp = partiallyEvaluate p in
  let tip = normalise pp tip in
    ti == tip
     
