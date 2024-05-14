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

import Control.Monad                (foldM_)
import Data.Maybe                   (fromMaybe)
import Data.List                    (isPrefixOf, isSuffixOf,
                                     intercalate, stripPrefix, sortBy)
import Data.Ord                     (comparing)
import qualified Data.Map.Strict as Map
import Data.SBV
import Data.SBV.Internals           (CV)


-- * Abbreviations
type PropertyDef = (P, Term Type)
type Property    = Term Type


-- * Export
check :: Bool -> RecursionDepth -> Program Type -> IO ()
check pretty depth program =
  -- For each property, collect the residual program
  -- and check next property with already specialised program
  foldM_ (checkProperty pretty depth) program (properties program)


checkProperty :: Bool -> RecursionDepth -> Program Type -> PropertyDef -> IO (Program Type)
checkProperty pretty depth prog (propName, prop) =
  do let symbol = if pretty then " ⇒ " else " >>> "
     putStr $ "Checking '" ++ propName ++ "'" ++ symbol
     let (prop', residual) = partiallyEvaluate prog prop
     let f = generateFormula depth residual prop'
     let reconstructor = indexReconstruct prog
     proveFormula pretty reconstructor f
     return residual


-- * Main functions
proveFormula :: Bool -> ((D, Integer) -> (D, C)) -> Symbolic SBool -> IO ()
proveFormula pretty reconstructor f =
  do let ok      = if pretty then " ✓" else ""
     let failed  = if pretty then " ✱" else ""
     let unknown = if pretty then " ●" else ""
     r@(ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> putStrLnGreen  $ ok     ++ " OK "
       Satisfiable   _ _ -> do putStrLnRed $ failed ++ " FAIL "
                               printCounterExample reconstructor $
                                 getModelDictionary result
       _                 -> do putStrLnYellow $ unknown ++ " Unknown result: "
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
                    "Unexpected error: Property should translate to a \
                    \Boolean formula, but was a " ++ show other


-- * Pretty-printing
printCounterExample :: ((D, Integer) -> (D, C)) -> Map.Map String CV -> IO ()
printCounterExample reconstructor m =
  do putStrLn "Counterexample:"
     putStrLn $ prettyPrint reconstructor (Map.toList m)
     putStrLn " "

prettyPrint :: ((D, Integer) -> (D, C)) -> [(Name, CV)] -> String
prettyPrint reconstructor assignments
  | null assignments  = "*** There are no variables bound by the model. ***"
  | null relevantVars = "*** There are no model-variables bound by the model. ***"
  | otherwise         = display $ parsePretty reconstructor relevantVars
  where
    relevantVars = sortBy (comparing fst) $ filter (not . ignore . fst) assignments
    ignore var  = "__internal_sbv" `isPrefixOf` var || '_' `elem` var

display :: [(Name, String)] -> String
display svs = intercalate "\n" $ map line svs
  where
    line (var, sv) = "  "
                      ++ justifyRight (longestName - length var) var
                      ++ " = "
                      ++ justifyLeft (longestVal - length sv) sv
    longestName = maximum $ 0 : [ length n  | (n, _ ) <- svs ]
    longestVal  = maximum $ 0 : [ length sv | (_, sv) <- svs ]
    justifyLeft  n s = s ++ replicate (n - length s) ' '
    justifyRight n s = replicate (n - length s) ' ' ++ s

parsePretty :: ((D, Integer) -> (D, C)) -> [(Name, CV)] -> [(Name, String)]
parsePretty _ [] = []
parsePretty reconstructor ((var, cv) : rest)
  | '$' `elem` var = let x         = takeWhile (/= '$') var                     in
                     let pretty    = prettyADT reconstructor ((var, cv) : rest) in
                     let remaining = filter ((not . isPrefixOf var) . fst) rest in
                          (x, pretty) : parsePretty reconstructor remaining
  | otherwise       = (var, show cv) : parsePretty reconstructor rest

splitAtChar :: Char -> String -> (String, String)
splitAtChar char str =
  let (before, after) = break (== char) str
  in  (before, drop 1 after)

prettyADT :: ((D, Integer) -> (D, C)) -> [(Name, CV)] -> String
prettyADT _ [] = ""
prettyADT reconstructor svs@((adtVar, _) : _) =
  let (x, adt)  = splitAtChar '$' adtVar                in
  let ctrs      = prettyConstructor reconstructor x svs in
    (ctrs ++ " " ++ " :: " ++ adt)

prettyConstructor :: ((D, Integer) -> (D, C)) -> Name -> [(Name, CV)] -> String
prettyConstructor _ _ [] = ""
prettyConstructor reconstructor prefix ((var, cv) : rest)
  | prefix `isPrefixOf` var =
    let var'     = fromMaybe "" $ stripPrefix prefix var   in
    let adt      = takeWhile (/= '$') (drop 1 var')        in
    let (_, ctr) = reconstructor (adt, getSelector cv)     in
    let fields   = prettyField reconstructor var rest      in
        (ctr ++ " " ++ braces (stripRedundant fields))
  | otherwise = prettyConstructor reconstructor prefix rest
  where
    braces = ("{" ++) . (++ "}")
    stripRedundant s
      | ", " `isSuffixOf` s = fromMaybe ""  $ stripSuffix ", " s
      | otherwise           = s
    stripSuffix a b = reverse <$> stripPrefix (reverse a) (reverse b)

prettyField :: ((D, Integer) -> (D, C)) -> Name -> [(Name, CV)] -> String
prettyField _ _ [] = ""
prettyField reconstructor prefix ((var, cv) : rest)
  | (prefix ++ "$field") `isPrefixOf` var =
    let prefix' = (prefix ++ "$field")                  in
    let var'   = fromMaybe "" $ stripPrefix prefix' var in
    let num     = takeWhile (/= '$') var'               in
      if (prefix' ++ num) == var
         then getVal cv ++ ", " ++ prettyField reconstructor prefix rest
         else prettyConstructor reconstructor (prefix' ++ num) ((var, cv) : rest)
  | otherwise = prettyConstructor reconstructor prefix ((var, cv) : rest)

getSelector :: CV -> Integer
getSelector s = read (takeWhile (/= ' ') $ show s) :: Integer

getVal :: CV -> String
getVal cv = takeWhile (/= ' ') $ show cv

