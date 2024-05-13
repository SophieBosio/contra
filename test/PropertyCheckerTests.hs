module PropertyCheckerTests where

import Core.Syntax
import Validation.Formula         (defaultRecDepth)
import Validation.PropertyChecker

import Test.Tasty
import Test.Tasty.HUnit
import Data.SBV


-- Export: Test groups
simple :: TestTree
simple =
  testGroup "Checking simple properties: " $
       commutativity
    ++ associativity

programs :: TestTree
programs =
  testGroup "Testing properties from example programs " $
       allTheorem
    ++ allFalsifiable


-- Helpers
theorem :: Term Type -> Assertion
theorem prop =
  do let f = generateFormula defaultRecDepth End prop
     (ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> return ()
       _                 -> assertFailure "Should be theorem."

falsifiable :: Term Type -> Assertion
falsifiable prop =
  do let f = generateFormula defaultRecDepth End prop
     (ThmResult result) <- prove f
     case result of
       Satisfiable _ _ -> return ()
       _               -> assertFailure "Should be falsifiable."


-- Simple tests
commutativity :: [TestTree]
commutativity =
  map (testCase "Checking commutativity: " . theorem)
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
    (Integer' :->: (Integer' :->: Boolean')) ]

associativity :: [TestTree]
associativity =
  map (testCase "Checking associativity: " . theorem)
    -- associativity
  [ Lambda (Variable "x" Integer')
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


-- Examples from the example programs in 'contra/examples'
allTheorem :: [TestTree]
allTheorem =
  map (\(p, prop) -> testCase ("Checking true property '" ++ p ++ "'") $
        theorem prop)
      -- From file 'contra/examples/trivialProperties.con'
    [ ("eqReflexive"
      , Lambda (Variable "x" Integer') (Equal (Pattern (Variable "x" Integer')) (Pattern (Variable "x" Integer')) Boolean') (Integer' :->: Boolean'))
    , ("addOneGt"
      , Lambda (Variable "x" Integer') (Gt (Plus (Pattern (Variable "x" Integer')) (Pattern (Value (Number 1 Integer'))) Integer') (Pattern (Variable "x" Integer')) Boolean') (Integer' :->: Boolean'))
    , ("subOneLt"
      , Lambda (Variable "x" Integer') (Lt (Minus (Pattern (Variable "x" Integer')) (Pattern (Value (Number 1 Integer'))) Integer') (Pattern (Variable "x" Integer')) Boolean') (Integer' :->: Boolean'))
      -- From file 'contra/examples/logic.con'
    , ("deMorgan-1"
      , Lambda (Variable "p" Boolean') (Lambda (Variable "q" Boolean') (Equal (Not (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Pattern (Variable "p" Boolean')) (Boolean' :->: Boolean')) (Pattern (Variable "q" Boolean')) Boolean') Boolean') (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Not (Pattern (Variable "p" Boolean')) Boolean') (Boolean' :->: Boolean')) (Not (Pattern (Variable "q" Boolean')) Boolean') Boolean') Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean')))
    , ("deMorgan-2"
      , Lambda (Variable "p" Boolean') (Lambda (Variable "q" Boolean') (Equal (Not (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Pattern (Variable "p" Boolean')) (Boolean' :->: Boolean')) (Pattern (Variable "q" Boolean')) Boolean') Boolean') (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Not (Pattern (Variable "p" Boolean')) Boolean') (Boolean' :->: Boolean')) (Not (Pattern (Variable "q" Boolean')) Boolean') Boolean') Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean')))
    , ("deMorgan-1-alt"
      , Lambda (Variable "p" Boolean') (Lambda (Variable "q" Boolean') (Equal (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Pattern (Variable "p" Boolean')) (Boolean' :->: Boolean')) (Pattern (Variable "q" Boolean')) Boolean') (Not (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Not (Pattern (Variable "p" Boolean')) Boolean') (Boolean' :->: Boolean')) (Not (Pattern (Variable "q" Boolean')) Boolean') Boolean') Boolean') Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean')))
    , ("deMorgan2-alt"
      , Lambda (Variable "p" Boolean') (Lambda (Variable "q" Boolean') (Equal (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Pattern (Variable "p" Boolean')) (Boolean' :->: Boolean')) (Pattern (Variable "q" Boolean')) Boolean') (Not (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Not (Pattern (Variable "p" Boolean')) Boolean') (Boolean' :->: Boolean')) (Not (Pattern (Variable "q" Boolean')) Boolean') Boolean') Boolean') Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean')))
    , ("excludedMiddle"
      , Lambda (Variable "p" Boolean') (Application (Application (Lambda (Variable "*a" Boolean') (Lambda (Variable "*b" Boolean') (Case (Pattern (List [Variable "*a" Boolean',Variable "*b" Boolean'] (TypeList [Boolean',Boolean']))) [(List [Value (Boolean True Boolean'),Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Value (Boolean True Boolean')] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean True Boolean'))),(List [Variable "x" Boolean',Variable "y" Boolean'] (TypeList [Boolean',Boolean']),Pattern (Value (Boolean False Boolean')))] Boolean') (Boolean' :->: Boolean')) (Boolean' :->: (Boolean' :->: Boolean'))) (Pattern (Variable "p" Boolean')) (Boolean' :->: Boolean')) (Not (Pattern (Variable "p" Boolean')) Boolean') Boolean') (Boolean' :->: Boolean'))
    ]

allFalsifiable :: [TestTree]
allFalsifiable =
  map (\(p, prop) -> testCase ("Checking falsifiable property '" ++ p ++ "'") $
        falsifiable prop)
    [ ("subAssociative"
      , Lambda (Variable "a" Integer')
          (Lambda (Variable "b" Integer')
            (Lambda (Variable "c" Integer')
             (Equal (Minus (Minus (Pattern (Variable "a" Integer'))
                            (Pattern (Variable "b" Integer')) Integer')
                      (Pattern (Variable "c" Integer')) Integer')
               (Minus (Pattern (Variable "a" Integer'))
                (Minus (Pattern (Variable "b" Integer'))
                 (Pattern (Variable "c" Integer')) Integer') Integer') Boolean')
              (Integer' :->: Boolean'))
            (Integer' :->: (Integer' :->: Boolean')))
        (Integer' :->: (Integer' :->: (Integer' :->: Boolean'))))
    , ("eqFalsifiable"
      , Lambda (Variable "x" Integer') (Lambda (Variable "y" Integer') (Equal (Pattern (Variable "x" Integer')) (Pattern (Variable "y" Integer')) Boolean') (Integer' :->: Boolean')) (Integer' :->: (Integer' :->: Boolean')))
    , ("gtFalsifiable"
      , Lambda (Variable "x" Integer') (Lambda (Variable "y" Integer') (Gt (Pattern (Variable "x" Integer')) (Pattern (Variable "y" Integer')) Boolean') (Integer' :->: Boolean')) (Integer' :->: (Integer' :->: Boolean')))
    , ("ltFalsifiable"
      , Lambda (Variable "x" Integer') (Lambda (Variable "y" Integer') (Lt (Pattern (Variable "x" Integer')) (Pattern (Variable "y" Integer')) Boolean') (Integer' :->: Boolean')) (Integer' :->: (Integer' :->: Boolean')))
    ]
