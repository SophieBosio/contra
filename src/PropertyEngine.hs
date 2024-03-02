{-# LANGUAGE FlexibleContexts #-}

module PropertyEngine where

import Syntax
import PartialEvaluator (partiallyEvaluate)

import Control.Monad.Reader
import Data.SBV


-- Abbreviations
type Input   = Term Type
type Formula = Reader Input


-- Export
check :: Program Type -> IO ()
check program =
  -- For each property, collect the residual program
  -- and check next property with already specialised program
  foldM_ checkProp program (properties program)


checkProp :: Program Type -> (P, Term Type) -> IO (Program Type)
checkProp prog (propName, prop) =
  do putStr $ "Testing " ++ propName ++ " ❯ "
     -- Inline function definitions used in the property
     let (prop', residual) = partiallyEvaluate prog prop
     -- Generate formula from term
     let f = generateFormula prop'
     -- Prove formula
     proveFormula f
     -- Return residual program for memoisation
     return residual


-- Main functions
proveFormula :: Provable a => a -> IO ()
proveFormula f =
  do result <- prove f
     if not (modelExists result)
       then putStrLnGreen  " ✓ OK "
       else do putStrLnRed " ✱ FAIL "
               putStrLn "\tCounterexample: "
               putStr "\t"
               print result -- TODO: Translate back into pretty terms

generateFormula :: Term Type -> SBool
generateFormula property = runReader (translate property) property
  -- do cs <- constraints program property


-- Constraint generation
-- translate :: Term Type -> Formula (SBV (Term Type))
-- translate (Equal t0 t1 _) =
--   do t0' <- translate t0
--      t1' <- translate t1
--      return $ t0' .== t1'
-- translate (Lt t0 t1 _) =
--   do t0' <- translate t0
--      t1' <- translate t1
--      return $ t0' .< t1'
-- translate (Gt t0 t1 _) =
--   do t0' <- translate t0
--      t1' <- translate t1
--      return $ t0' .> t1'
-- translate (Lambda x t0 a) =  
-- translate (Application t1 t2 _) =
translate :: Term Type -> Formula (SBool)
translate = undefined


-- Utility
putStrLnRed :: String -> IO ()
putStrLnRed s = putStrLn $ "\ESC[91m\STX" ++ s ++ "\ESC[m\STX"

putStrLnGreen :: String -> IO ()
putStrLnGreen s = putStrLn $ "\ESC[92m\STX" ++ s ++ "\ESC[m\STX"
