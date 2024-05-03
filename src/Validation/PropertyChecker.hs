{-

  Module      : Validation.PropertyChecker
  Description : PropertyChecker for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  The PropertyChecker is the driver for the property-checking code, which is
  primarily the Translator.

  Its main functions are:
   * 'check'
   * 'checkProperty'
   * 'generateFormula'
   * 'realise'
   * 'proveFormula'

  'check' checks all the properties in a program by calling 'checkProperty'
  on each property and collecting the residual (partially evaluated) program
  for each call.

  'checkProperty' checks a single property by partially evaluating the property
  wrt. the program text, generating an SValue formula, converting it back to
  an SBV formula, proving the formula, and returning the partially evaluated
  program.

  'generateFormula' calls 'translateToFormula' from Validation.Translator to
  generate an SValue formula.

  'realise' turns that SValue formula into an SBV formula.

  'proveFormula' asks the SMT solver, via the SBV bindings, to prove the
  generated formula, which succeeds, returns a counterexample, or produces
  an unknown result.

-}

{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, LambdaCase #-}

module Validation.PropertyChecker where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.ERSymbolic
import Validation.Formula
import Validation.Translator

import Control.Monad (foldM_)
import Data.SBV


-- Abbreviations
type PropertyDef = (P, Term Type)
type Property    = Term Type


-- Export
check :: RecursionDepth -> Program Type -> IO ()
check depth program =
  -- For each property, collect the residual program
  -- and check next property with already specialised program
  foldM_ (checkProperty depth) program (properties program)


checkProperty :: RecursionDepth -> Program Type -> PropertyDef -> IO (Program Type)
checkProperty depth prog (propName, prop) =
  do putStr $ "Checking '" ++ propName ++ "' ❯ "
     let (prop', residual) = partiallyEvaluate prog prop
     let f = generateFormula depth residual prop' 
     proveFormula f
     return residual


-- Main functions
proveFormula :: Symbolic SBool -> IO ()
proveFormula f =
  do r@(ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> putStrLnGreen  " ✓ OK "
       Satisfiable   _ _ -> do putStrLnRed " ✱ FAIL "
                               putStr " "
                               print r
                               -- TODO: printCounterExample m
       _                 -> do putStrLnYellow " ● Unknown result: "
                               print r

generateFormula :: RecursionDepth -> Program Type -> Property -> Symbolic SBool
generateFormula depth program prop =
  let sValueFormula =
        runFormula (translateToFormula depth prop) program emptyBindings
  in  realise sValueFormula


-- Realise 'SValue' formula as an SBV 'SBool' formula
realise :: Symbolic SValue -> Symbolic SBool
realise sv =
  sv >>= \case
    (SBoolean b) -> return b
    other        -> error $
                    "Unexpected error: Property should translate to a\
                    \Boolean formula, but was a " ++ show other

