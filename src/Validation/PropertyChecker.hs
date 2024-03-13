{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}

module Validation.PropertyChecker where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.ERWS hiding (local)

import Control.Monad.Reader
import Data.SBV


-- Abbreviations
type Bindings   = Mapping X SValue
-- type Constraint = Reader Bindings
-- type Model      = Symbolic
type Formula  a = ReaderT Bindings Symbolic a
-- type Correspondence = Mapping Type SType
data SValue =
    SUnit
  | SBoolean SBool
  | SNumber  SInteger
  | SName    SString
  | SCtrArgs [SValue]


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
proveFormula :: Symbolic SBool -> IO ()
proveFormula f =
  do result <- prove f
     if not (modelExists result)
       then putStrLnGreen  " ✓ OK "
       else do putStrLnRed " ✱ FAIL "
               putStrLn "\tCounterexample: "
               putStr "\t"
               print result

generateFormula :: Term Type -> Formula SBool
-- generateFormula = undefined
generateFormula p =
  do p' <- liftInputVars p
     translateProp p'
-- generateFormula property = runReader (translate property) property
  -- do cs <- constraints program property


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftInputVars :: Term Type -> Formula (Term Type)
liftInputVars (Lambda (Variable x tau) t _) =
  do sx <- fresh x tau
     local (bind x sx) $ liftInputVars t

-- liftInputVars :: Term Type -> Bindings
-- liftInputVars (Lambda (Variable x tau) t _) = bind x tau $ liftInputVars t
-- -- liftInputVars (Lambda (PConstructor c xs tau) t _) = 

bind :: X -> SValue -> X `MapsTo` SValue
bind = undefined
-- bind x tau look y = if x == y then fresh x tau else look y

fresh :: X -> Type -> Formula SValue
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
translateProp :: Term Type -> Formula SBool
translateProp = undefined

translate :: Term Type -> Formula SValue
translate (Pattern    p) = translatePattern p
translate (Plus t0 t1 _) =
  do t0' <- translate t0 >>= numeric
     t1' <- translate t1 >>= numeric
     return $ SNumber $ t0' + t1'
translate (Minus t0 t1 _) =
  do t0' <- translate t0 >>= numeric
     t1' <- translate t1 >>= numeric
     return $ SNumber $ t0' - t1'
translate (Lt t0 t1 _) =
  do t0' <- translate t0 >>= numeric
     t1' <- translate t1 >>= numeric
     return $ SBoolean $ t0' .< t1'
translate (Gt t0 t1 _) =
  do t0' <- translate t0 >>= numeric
     t1' <- translate t1 >>= numeric
     return $ SBoolean $ t0' .> t1'
translate (Equal t0 t1 _) =
  do t0' <- translate t0 >>= numeric
     t1' <- translate t1 >>= numeric
     return $ SBoolean $ t0' .== t1'
translate (Not t0 _) =
  do t0' <- translate t0 >>= boolean
     return $ SBoolean $ sNot t0'

translatePattern :: Pattern Type -> Formula SValue
translatePattern (Value v) = translateValue v
-- translatePattern (Variable x a) =
  -- do bindings <- ask
-- translatePattern (PConstructor c ps a) =
-- TODO: translatePattern

translateValue :: Value a -> Formula SValue
translateValue (Unit      _) = return SUnit
translateValue (Number  n _) = return $ SNumber  $ literal n
translateValue (Boolean b _) = return $ SBoolean $ literal b
-- translateValue (VConstructor c vs a) = TODO: Constructor magic!


-- Utility
truthy :: SValue -> SBool
truthy (SBoolean b) = b

sEqual :: SValue -> SValue -> SValue
sEqual  SUnit         SUnit        = SBoolean sTrue
sEqual (SBoolean b ) (SBoolean c ) = SBoolean (b .== c)
sEqual (SNumber  n ) (SNumber  m ) = SBoolean (n .== m)
sEqual (SName    x ) (SName    y ) = SBoolean (x .== y)
sEqual (SCtrArgs xs) (SCtrArgs ys) = SBoolean $ sAnd $ map truthy $ zipWith sEqual xs ys

numeric :: SValue -> Formula SInteger
numeric = undefined

boolean :: SValue -> Formula SBool
boolean = undefined


-- Pretty printing
redStr :: String -> String
redStr s = "\ESC[31m\STX" ++ s ++ "\ESC[m\STX"

greenStr :: String -> String
greenStr s = "\ESC[32m\STX" ++ s ++ "\ESC[m\STX"

putStrLnRed :: String -> IO ()
putStrLnRed = putStrLn . redStr

putStrLnGreen :: String -> IO ()
putStrLnGreen = putStrLn . greenStr
