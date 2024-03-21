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

import Control.Monad (foldM_, liftM2)
import Control.Arrow ((***))
import Data.SBV


-- Abbreviations
data SValue =
    SUnit
  | SBoolean SBool
  | SNumber  SInteger
  | SCtr     String [SValue]
  deriving Show
type Bindings   = Mapping X SValue
type Formula  a = ERSym Type Bindings a


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
  let constraints = runFormula (formula p) program emptyBindings
  in  realise constraints


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftInputVars :: Term Type -> Formula ()
liftInputVars (Lambda (Variable x tau) t _) =
  do sx <- fresh x tau
     local (bind x sx) $ liftInputVars t
liftInputVars (Lambda (PConstructor c ps _) t _) =
  do mapM_ (liftInputVars . weakenToTerm) ps
     liftInputVars t
liftInputVars _ = return ()

bind :: X -> SValue -> X `MapsTo` SValue
bind x tau look y = if x == y then tau else look y

fresh :: X -> Type -> Formula SValue
fresh _ Unit'    = return SUnit
fresh x Integer' =
  do sx <- liftSymbolic $ sInteger x
     return $ SNumber sx
fresh x Boolean' =
  do sx <- liftSymbolic $ sBool x
     return $ SBoolean sx
fresh x (Variable' _) =
  do sx <- liftSymbolic $ free x
     return $ SNumber sx
-- fresh x (t1 :->: t2) =
-- fresh x (ADT t) =
--   do env <- environment
-- To generate a fresh ADT variable, you could maybe generate a list of possible constructors + their args


-- Constraint generation
formula :: Term Type -> Formula SValue
formula p = liftInputVars p >> translate p

translate :: Term a -> Formula SValue
translate (Pattern    p) = translatePattern p
-- translate (Lambda p t _) = _
-- https://hackage.haskell.org/package/sbv-10.5/docs/Data-SBV.html#g:40
-- translate (Application t1 t2 _) = _
-- translate (Let p t1 t2 _) = _
translate (Case t0 ts _) =
  do t0' <- translate t0
     let translatePair = (translate . weakenToTerm) *** translate
     let ts' = map translatePair ts
     ts'' <- mapM (uncurry (liftM2 (,))) ts'
     return $ branches t0' ts''
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
  do t0' <- translate t0
     t1' <- translate t1
     return $ t0' `sEqual` t1'
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
translatePattern (PConstructor c ps _) =
  do sps <- mapM translatePattern ps
     return $ SCtr c sps

translateValue :: Value a -> Formula SValue
translateValue (Unit      _) = return SUnit
translateValue (Number  n _) = return $ SNumber  $ literal n
translateValue (Boolean b _) = return $ SBoolean $ literal b
translateValue (VConstructor c vs _) =
  do svs <- mapM translateValue vs
     return $ SCtr c svs


-- Translation helpers
numeric :: SValue -> Formula SInteger
numeric (SNumber n) = return n
numeric sv          = error $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error $ "Expected a boolean symval, but got " ++ show sv

branches :: SValue -> [(SValue, SValue)] -> SValue
branches _ [] = error "Non-exhaustive patterns in case statement"
branches v ((p, t) : rest) =
  merge (symUnify v p) (substituteIn t v p) $ branches v rest


-- SValue unification & substitution
-- TODO: symUnify
symUnify :: SValue -> SValue -> SBool
symUnify = undefined

-- TODO: substituteIn
substituteIn :: SValue -> SValue -> SValue -> SValue
substituteIn = undefined

merge :: SBool -> SValue -> SValue -> SValue
merge _  SUnit        SUnit       = SUnit
merge b (SNumber  x) (SNumber  y) = SNumber  $ ite b x y
merge b (SBoolean x) (SBoolean y) = SBoolean $ ite b x y
merge b (SCtr  x xs) (SCtr  y ys)
  | x == y    = SCtr x $ mergeList b xs ys
  | otherwise = error $ "Mismatching type constructors '"
                ++ show x ++ "' and '" ++ show y ++ "'"
merge _ x y = error $ "Type mismatch between symbolic values '"
              ++ show x ++ "' and '" ++ show y ++ "'"

mergeList :: SBool -> [SValue] -> [SValue] -> [SValue]
mergeList sb xs ys
  | Just b <- unliteral sb = if b then xs else ys
  | otherwise              = error $ "Unable to merge constructor arguments '"
                             ++ show xs ++ "' with '" ++ show ys ++ "'"

-- Constraint realisation
-- Realise 'SValue' as an 'SBool'
-- TODO: realise constraints
realise :: Symbolic SValue -> Symbolic SBool
realise sv =
  do v <- sv
     case v of
       (SBoolean b) -> return b
       other        -> error "Property should translate to a Boolean formula, but was a "


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


-- Pretty printing
-- printCounterExample :: SMTModel -> IO ()
-- https://hackage.haskell.org/package/sbv-10.5/docs/Data-SBV.html#g:58
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
