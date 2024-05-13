module UnificationTests where

import Core.Syntax
import Analysis.Unification

import Test.Tasty
import Test.Tasty.HUnit


-- Export
substitutionTests :: TestTree
substitutionTests =
  testGroup "Computing a substitution -- t[v/x]: " $
       substituteVars
    ++ substituteADTs


-- Helpers
computeSubstitutionOK :: (Show a, Eq a) => Pattern a -> Term a
                                        -> Term a -> Term a -> Assertion
computeSubstitutionOK x t v e =
  -- Computing 'v' in 't' instead of 'x' should give 'e'
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

substituteADTs :: [TestTree]
substituteADTs =
  map (\(x, t, v, e) -> testCase
                        ("(" ++ show t ++ ")[" ++ show v ++ "/" ++ show x ++ "]" ++
                         " should give " ++ show e) $
                        computeSubstitutionOK x t v e)
  [ ( Variable "x" ()
    , TConstructor "C" [TConstructor "D" [TConstructor "E" [Pattern (Variable "x" ())] ()] ()] ()
    , Pattern (Value (Number 5 ()))
    , TConstructor "C" [TConstructor "D" [TConstructor "E" [Pattern (Value (Number 5 ()))] ()] ()] ())
  , ( Variable "x" ()
    , TConstructor "C" [TConstructor "D" [TConstructor "E" [Pattern (Variable "x" ())] ()] ()] ()
    , Pattern (Value (VConstructor "F" [Number 10 (), Boolean True ()] ()))
    , TConstructor "C" [TConstructor "D" [TConstructor "E" [Pattern (Value (VConstructor "F" [Number 10 (), Boolean True ()] ()))] ()] ()] ())
  ]
