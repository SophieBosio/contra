module InterpreterTests where

-- import Syntax
-- import Interpreter

import Test.Tasty
-- import Test.Tasty.HUnit
-- import Test.Tasty.QuickCheck as QC

interpreterTests :: TestTree
interpreterTests =
  testGroup "Main interpreter tests: "
    [
    ]

-- TODO! Equivalence of terms
-- Also probably, 'normalise' should return a Pattern, not a Term

-- patternsNormaliseOK :: Show a => Program a -> Term a -> Term a -> TestTree
-- patternsNormaliseOK program term expected =
--   testCase (show term ++ " should normalise to " ++ show expected) $
--     normalise program term @?= expected

-- patternsNormaliseBAD :: TestTree
-- patternsNormaliseBAD = undefined

