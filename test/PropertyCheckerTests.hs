module PropertyCheckerTests where

import Core.Syntax
import Semantics.PartialEvaluator
import Validation.PropertyChecker

import Test.Tasty
import Test.Tasty.HUnit
import Data.SBV


-- Export: Test groups
simple :: TestTree
simple =
  testGroup "Checking simple properties: " $
       simpleSatisfiableProps
    ++ simpleUnsatisfiableProps


-- Helpers
satisfiable :: Term Type -> Assertion
satisfiable prop =
  do let f = generateFormula prop
     (ThmResult result) <- prove f
     case result of
       Satisfiable _ _ -> return ()
       _               -> assertFailure "Should be satisfiable."

unsatisfiable :: Term Type -> Assertion
unsatisfiable prop =
  do let f = generateFormula prop
     (ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> return ()
       _                 -> assertFailure "Should be unsatisfiable."


-- Tests
simpleSatisfiableProps :: [TestTree]
simpleSatisfiableProps =
  map (\p -> testCase ("Checking property '" ++ show p ++ "'")
             (satisfiable p))
    -- commutativity
  [ Lambda (Variable "x" Integer')
    (Lambda (Variable "y" Integer')
      (Equal
        (Plus
          (Pattern (Variable "x" Integer'))
          (Pattern (Variable "y" Integer'))
          Integer')
        (Plus
          (Pattern (Variable "y" Integer'))
          (Pattern (Variable "x" Integer'))
          Integer')
        Boolean')
      (Integer' :->: Boolean'))
    (Integer' :->: (Integer' :->: Boolean'))
    -- associativity
  , Lambda (Variable "x" Integer')
    (Lambda (Variable "y" Integer')
      (Lambda (Variable "z" Integer')
        (Equal
          (Plus
            (Plus
              (Pattern (Variable "x" Integer'))
              (Pattern (Variable "y" Integer')) Integer')
            (Pattern (Variable "z" Integer')) Integer')
          (Plus
            (Pattern (Variable "x" Integer'))
            (Plus
              (Pattern (Variable "y" Integer'))
              (Pattern (Variable "z" Integer')) Integer')
            Integer')
          Boolean')
        (Integer' :->: Boolean'))
      (Integer' :->: (Integer' :->: Boolean')))
    (Integer' :->: (Integer' :->: (Integer' :->: Boolean')))
    -- right identity
  , Lambda (Variable "x" Integer')
    (Equal
      (Plus
        (Pattern (Variable "x" Integer'))
        (Pattern (Value (Number 0 Integer'))) Integer')
      (Pattern (Variable "x" Integer')) Boolean')
    (Integer' :->: Boolean')
    -- left identity
  , Lambda (Variable "x" Integer')
    (Equal
      (Plus
        (Pattern (Value (Number 0Integer')))
        (Pattern (Variable "x" Integer')) Integer')
      (Pattern (Variable "x" Integer')) Boolean')
    (Integer' :->: Boolean')
  ]

simpleUnsatisfiableProps :: [TestTree]
simpleUnsatisfiableProps = []
