{-# LANGUAGE FlexibleContexts #-}

module PropertyEngine where

import Syntax
import PartialEvaluator (partiallyEvaluate)

import Control.Monad    (foldM_)
import Data.SBV


-- Abbrevations
data Prover a = Prover {}


-- Export
check :: Program Type -> IO ()
check program =
  -- For each property, collect the residual program
  -- and check next property with already specialised program
  foldM_ checkProp program (properties program)


checkProp :: Program Type -> (P, Term Type) -> IO (Program Type)
checkProp prog (propName, prop) =
  do putStr $ "Testing " ++ propName ++ " ❯ "
     let (prop', residual) = partiallyEvaluate prog prop
     let f = generateFormula residual prop'
     proveFormula f
     return residual


-- Main functions
proveFormula :: Provable a => a -> IO ()
proveFormula f =
  do result <- prove f
     if modelExists result
       then putStrLnGreen  " ✓ OK "
       else do putStrLnRed " ✱ FAIL "
               putStrLn "Counterexample: "
               print result -- TODO: Translate back into pretty terms

generateFormula :: Program Type -> Term Type -> SBool
generateFormula program property = undefined
  -- do cs <- constraints program property


-- Utility
putStrLnRed :: String -> IO ()
putStrLnRed s = putStrLn $ "\ESC[91m\STX" ++ s ++ "\ESC[m\STX"

putStrLnGreen :: String -> IO ()
putStrLnGreen s = putStrLn $ "\ESC[92m\STX" ++ s ++ "\ESC[m\STX"
