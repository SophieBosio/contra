{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}

module Validation.PropertyChecker where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.ERWS hiding (local, ask)

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
  deriving Show


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
  do r@(ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> putStrLnGreen  " ✓ OK "
       Satisfiable   _ m -> do putStrLnRed " ✱ FAIL "
                               putStrLn "\tCounterexample: "
                               putStr "\t"
                               print r
                               -- TODO: printCounterExample m
       smtresult         -> do putStrLn " ⭕︎ Unexpected result: "
                               print r

generateFormula :: Term Type -> Formula SBool
-- generateFormula = undefined
generateFormula p =
  do p' <- liftInputVars p
     formula p'
-- generateFormula property = runReader (translate property) property
  -- do cs <- constraints program property


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftInputVars :: Term Type -> Formula (Term Type)
liftInputVars (Lambda (Variable x tau) t _) =
  do sx <- fresh x tau
     local (bind x sx) $ liftInputVars t

bind :: X -> SValue -> X `MapsTo` SValue
bind = undefined
-- bind x tau look y = if x == y then fresh x tau else look y

fresh :: X -> Type -> Formula SValue
fresh _ Unit'    = return SUnit
fresh x Integer' =
  do sx <- lift $ sInteger x
     return $ SNumber sx
fresh x Boolean' =
  do sx <- lift $ sBool x
     return $ SBoolean sx
fresh x (Variable' _) =
  do sx <- lift $ free x
     return $ SNumber sx
-- fresh x (t1 :->: t2) =
-- fresh x (ADT x) =


-- Constraint generation
formula :: Term Type -> Formula SBool
formula = undefined
-- formula (Case ) = ...

translate :: Term a -> Formula SValue
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

translatePattern :: Pattern a -> Formula SValue
translatePattern (Value v) = translateValue v
-- All input variables are bound at this point,
-- so if a variable is not in the bindings, that's an error
translatePattern (Variable x _) =
  do bindings <- ask
     return $ bindings x
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
truthy v = error $ "Expected a symbolic boolean value, but got " ++ show v

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
-- printCounterExample :: SMTModel -> IO ()
printCounterExample = undefined

redStr :: String -> String
redStr s = "\ESC[31m\STX" ++ s ++ "\ESC[m\STX"

greenStr :: String -> String
greenStr s = "\ESC[32m\STX" ++ s ++ "\ESC[m\STX"

putStrLnRed :: String -> IO ()
putStrLnRed = putStrLn . redStr

putStrLnGreen :: String -> IO ()
putStrLnGreen = putStrLn . greenStr
