module PropertyCheckerTests where

import Core.Syntax
import Semantics.PartialEvaluator
import Validation.PropertyChecker

import Test.Tasty
import Test.Tasty.HUnit
import Data.SBV


-- Export: Test groups
simple :: TestTree
simple = undefined


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

