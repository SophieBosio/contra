module PropertyCheckerTests where

import Core.Syntax
import Semantics.PartialEvaluator
import Validation.PropertyChecker

import Test.Tasty
import Test.Tasty.HUnit


-- Export: Test groups
simple :: TestTree
simple = undefined


-- Helpers
satisfiable :: Program Type -> Term Type -> Assertion
satisfiable prog prop = undefined

unsatisfiable :: Program Type -> Term Type -> Assertion
unsatisfiable = undefined


-- Tests

