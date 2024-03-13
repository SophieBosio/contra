{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}

module Validation.PropertyEngine where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.ERWS

import Control.Monad.Reader
import Data.SBV


-- Abbreviations
type Bindings   = Mapping X SValue
-- type Constraint = Reader Bindings
-- type Model      = Symbolic
type Formula  a = ReaderT Bindings Symbolic a
-- type Correspondence = Mapping Type SType
data SValue =
    SBoolean SBool
  | SNumber  SInteger
  | SName    SString
  | SParams  [SValue]


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
     let f = runReaderT (generateFormula prop') emptyBindings
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
               print result

generateFormula :: Term Type -> Formula SBool
generateFormula = undefined
-- generateFormula p =
--   do inputVars <- liftInputVars p
--      translate p
-- generateFormula property = runReader (translate property) property
  -- do cs <- constraints program property


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftInputVars :: Term Type -> Bindings
liftInputVars (Lambda (Variable x tau) t _) = bind x tau $ liftInputVars t
-- liftInputVars (Lambda (PConstructor c xs tau) t _) = 

bind :: X -> Type -> X `MapsTo` SValue
bind x tau look y = if x == y then fresh x tau else look y

fresh :: X -> Type -> SValue
fresh = undefined
-- fresh x Unit' =
--   do b <- sTrue x
     
-- fresh x Integer' =
--   do sx <- sInteger x
--      SNumeric sx
-- fresh x Boolean' =
--   do sx <- lift $ sBool x
--      return $ SB sx
-- -- fresh x (ADT t)


-- Constraint generation
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
