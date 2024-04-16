{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, LambdaCase #-}

module Validation.PropertyChecker where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.ERSymbolic
import Validation.Formula
import Validation.Translator

import Control.Monad (foldM_)
import Data.SBV


-- Export
check :: Program Type -> IO ()
check program =
  -- For each property, collect the residual program
  -- and check next property with already specialised program
  foldM_ checkProperty program (properties program)


checkProperty :: Program Type -> (P, Term Type) -> IO (Program Type)
checkProperty prog (propName, prop) =
  do putStr $ "Testing " ++ propName ++ " ❯ "
     let (prop', residual) = partiallyEvaluate prog prop
     let f = generateFormula residual prop'
     proveFormula f
     return residual


-- Main functions
proveFormula :: Symbolic SBool -> IO ()
proveFormula f =
  do r@(ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> putStrLnGreen  " ✓ OK "
       Satisfiable   _ _ -> do putStrLnRed " ✱ FAIL "
                               putStrLn "\tCounterexample: "
                               putStr "\t"
                               print r
                               -- TODO: printCounterExample m
       _                 -> do putStrLnYellow " ● Unexpected result: "
                               print r

generateFormula :: Program Type -> Term Type -> Symbolic SBool
generateFormula program p =
  let sValueFormula = runFormula (formula p) program emptyBindings
  in  realise sValueFormula


-- Realise 'SValue' as an 'SBool'
realise :: Symbolic SValue -> Symbolic SBool
realise sv =
  sv >>= \case
    (SBoolean b) -> return b
    other        -> error $
                    "Property should translate to a Boolean formula, but was a "
                    ++ show other


-- Pretty printing
-- printCounterExample :: SMTModel -> IO ()
-- https://hackage.haskell.org/package/sbv-10.5/docs/Data-SBV.html#g:58
-- TODO: printCounterExample = undefined

redStr :: String -> String
redStr s = "\ESC[31m\STX" ++ s ++ "\ESC[m\STX"

yellowStr :: String -> String
yellowStr s = "\ESC[33m\STX" ++ s ++ "\ESC[m\STX"

greenStr :: String -> String
greenStr s = "\ESC[32m\STX" ++ s ++ "\ESC[m\STX"

putStrLnRed :: String -> IO ()
putStrLnRed = putStrLn . redStr

putStrLnYellow :: String -> IO ()
putStrLnYellow = putStrLn . yellowStr

putStrLnGreen :: String -> IO ()
putStrLnGreen = putStrLn . greenStr
