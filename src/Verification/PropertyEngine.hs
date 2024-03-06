{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Verification.PropertyEngine where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.ERWS

import Control.Monad.Reader
import Data.SBV


-- Abbreviations
type Bindings   = Mapping X SInteger
-- type Constraint = Reader Bindings
-- type Model      = Symbolic
type Formula  a = ReaderT Bindings Symbolic a
-- type Correspondence = Mapping Type SType
data SValue =
    SB SBool
  | SI SInteger
  | SN SString
  | SL (SList SValue)


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
     let f = runReaderT (generateFormula prop') liftInputVars
     -- -- Prove formula
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

generateFormula :: Term Type -> Formula SBool
generateFormula = undefined
-- generateFormula property = runReader (translate property) property
  -- do cs <- constraints program property


-- Constraint generation
liftInputVars :: Bindings
liftInputVars = undefined

fresh :: X -> Type -> Formula SValue
fresh _ Unit' = return $ SB sTrue
fresh x Integer' =
  do sx <- lift $ sInteger x
     return $ SI sx
fresh x Boolean' =
  do sx <- lift $ sBool x
     return $ SB sx
-- fresh x (ADT t)

translate :: Term Type -> Formula SInteger
translate (Plus t0 t1 _) =
  do t0' <- numeric t0
     t1' <- numeric t1
     return $ t0' + t1'
translate (Minus t0 t1 _) =
  do t0' <- numeric t0
     t1' <- numeric t1
     return $ t0' - t1'
translate (Lt t0 t1 _) =
  do t0' <- numeric t0
     t1' <- numeric t1
     return $ oneIf $ t0' .< t1'
translate (Gt t0 t1 _) =
  do t0' <- numeric t0
     t1' <- numeric t1
     return $ oneIf $ t0' .> t1'
translate (Equal t0 t1 _) =
  do t0' <- numeric t0
     t1' <- numeric t1
     return $ oneIf $ t0' .== t1'
translate (Not t0 _) =
  do t0' <- boolean t0
     return $ oneIf t0'

-- Translating values
numeric :: Term Type -> Formula SInteger
numeric (Pattern (Value (Number n _))) = return $ literal n
-- numeric (Pattern (Variable      x   _) = -- TODO: perform lookup
numeric t = do translate t


boolean :: Term Type -> Formula SBool
boolean (Pattern (Value (Boolean b _))) = return $ literal b
-- boolean (Pattern (Variable       x  _)) = -- TODO: perform lookup
boolean t =
  do t' <- translate t
     return $ if t' == 1 then sTrue else sFalse


-- Pretty printing
redStr :: String -> String
redStr s = "\ESC[31m\STX" ++ s ++ "\ESC[m\STX"

greenStr :: String -> String
greenStr s = "\ESC[32m\STX" ++ s ++ "\ESC[m\STX"

putStrLnRed :: String -> IO ()
putStrLnRed = putStrLn . redStr

putStrLnGreen :: String -> IO ()
putStrLnGreen = putStrLn . greenStr
