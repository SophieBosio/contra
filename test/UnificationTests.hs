module UnificationTests where

import Core.Syntax
import Analysis.Unifier

import Test.Tasty
import Test.Tasty.HUnit


-- Export
substitutionTests :: TestTree
substitutionTests =
  testGroup "Computing a substitution -- t[v/x]: "
    substituteVars


-- Helpers
computeSubstitutionOK :: (Show a, Eq a) => Pattern a -> Term a
                                        -> Term a -> Term a -> Assertion
computeSubstitutionOK x t v e =
  assertEqual "Should be equal after substitution."
    e (substitute x t v)


-- Substitution
substituteVars :: [TestTree]
substituteVars =
  map (\(x, t, v, e) -> testCase
                        ("(" ++ show t ++ ")[" ++ show v ++ "/" ++ show x ++ "]" ++
                         " should give " ++ show e) $
                        computeSubstitutionOK x t v e)
  [ ( Variable "x" ()
    , Plus (Pattern (Variable "x" ())) (Pattern (Value (Number 3 ()))) ()
    , Pattern (Value (Number 5 ()))
    , Plus (Pattern (Value (Number 5 ()))) (Pattern (Value (Number 3 ()))) ())
  , ( Variable "x" ()
    , Plus (Pattern (Variable "x" ())) (Pattern (Variable "y" ())) ()
    , Pattern (Value (Number 5 ()))
    , Plus (Pattern (Value (Number 5 ()))) (Pattern (Variable "y" ())) ())
  , ( PConstructor "Ctr" [Variable "x" (), Variable "y" ()] ()
    , Plus (Pattern (Variable "x" ())) (Pattern (Variable "y" ())) ()
    , TConstructor "Ctr" [Pattern (Value (Number 5 ())), Pattern (Value (Number 3 ()))] ()
    , Plus (Pattern (Value (Number 5 ()))) (Pattern (Value (Number 3 ()))) ())
  ]
