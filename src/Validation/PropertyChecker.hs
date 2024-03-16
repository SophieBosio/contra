{-# LANGUAGE
    FlexibleContexts,
    ScopedTypeVariables,
    TypeOperators,
    LambdaCase
#-}

module Validation.PropertyChecker where

import Core.Syntax
import Semantics.PartialEvaluator (partiallyEvaluate)
import Environment.Environment
import Environment.ERSym

-- import Control.Monad.Reader
import Control.Monad (foldM_)
import Data.SBV


-- Abbreviations
type Bindings   = Mapping X SValue
type Formula  a = ERSym Type Bindings a
data SValue     =
    SUnit
  | SBoolean SBool
  | SNumber  SInteger
  | SCtr     String [SValue]
  deriving Show


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
       Satisfiable   _ m -> do putStrLnRed " ✱ FAIL "
                               putStrLn "\tCounterexample: "
                               putStr "\t"
                               print r
                               -- TODO: printCounterExample m
       _                 -> do putStrLnYellow " ● Unexpected result: "
                               print r

generateFormula :: Program Type -> Term Type -> Symbolic SBool
generateFormula program p =
  do let constraints = runFormula (formula p) program emptyBindings
     realise constraints


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftInputVars :: Term Type -> Formula ()
liftInputVars (Lambda (Variable x tau) t _) =
  do sx <- fresh x tau
     local (bind x sx) $ liftInputVars t
-- TODO: liftInputVars (Lambda (PConstructor c ps tau) t _) =
liftInputVars t = return ()

bind :: X -> SValue -> X `MapsTo` SValue
bind x tau look y = if x == y then tau else look y

fresh :: X -> Type -> Formula SValue
fresh _ Unit'    = return SUnit
-- fresh x Integer' =
--   do sx <- lift $ sInteger x
--      return $ SNumber sx
-- fresh x Boolean' =
--   do sx <- lift $ sBool x
--      return $ SBoolean sx
-- fresh x (Variable' _) =
--   do sx <- lift $ free x
--      return $ SNumber sx
-- fresh x (t1 :->: t2) =
-- fresh x (ADT x) =


-- Constraint generation
formula :: Term Type -> Formula SValue
formula p = liftInputVars p >> translate p

translate :: Term a -> Formula SValue
translate (Pattern    p) = translatePattern p
-- translate (Lambda p t _) = _
-- translate (Application t1 t2 _) = _
-- translate (Let p t1 t2 _) = _
-- translate (Case t0 ts _) = _
translate (TConstructor c ts _) =
  do sts <- mapM translate ts
     return $ SCtr c sts
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
-- translate (Rec x t0 a) -- future work

translatePattern :: Pattern a -> Formula SValue
translatePattern (Value v) = translateValue v
-- All input variables are bound at this point,
-- so if a variable is not in the bindings, that's an error
translatePattern (Variable x _) =
  do bindings <- ask
     return $ bindings x
translatePattern (PConstructor c ps a) =
  do sps <- mapM translatePattern ps
     return $ SCtr c sps

translateValue :: Value a -> Formula SValue
translateValue (Unit      _) = return SUnit
translateValue (Number  n _) = return $ SNumber  $ literal n
translateValue (Boolean b _) = return $ SBoolean $ literal b
translateValue (VConstructor c vs a) =
  do svs <- mapM translateValue vs
     return $ SCtr c svs


-- Constraint realisation
-- Going from 'SValue' to 'SBool'
realise :: Symbolic SValue -> Symbolic SBool
realise sv = undefined


-- Utility
truthy :: SValue -> SBool
truthy (SBoolean b) = b
truthy v = error $ "Expected a symbolic boolean value, but got " ++ show v

sEqual :: SValue -> SValue -> SValue
sEqual  SUnit         SUnit        = SBoolean sTrue
sEqual (SBoolean  b) (SBoolean  c) = SBoolean (b .== c)
sEqual (SNumber   n) (SNumber   m) = SBoolean (n .== m)
sEqual (SCtr   x xs) (SCtr   y ys) = SBoolean $ sAnd $ fromBool (x == y)
                                     : map truthy (zipWith sEqual xs ys)
sEqual _             _             = SBoolean sFalse


numeric :: SValue -> Formula SInteger
numeric (SNumber n) = return n
numeric sv          = error $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error $ "Expected a boolean symval, but got " ++ show sv


-- Pretty printing
-- printCounterExample :: SMTModel -> IO ()
printCounterExample = undefined

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
