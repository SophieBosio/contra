module Validation.Translator where

import Core.Syntax
import Environment.ERSymbolic
import Validation.Formula
import Validation.SymUnifier

import Data.Foldable (foldrM)
import Data.SBV


-- Export
translateToFormula :: Term Type -> Formula SValue
translateToFormula prop =
  do (prop', bs) <- liftLambdaInputs prop
     local bs $ translate prop'


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftInput :: Pattern Type -> Formula (Bindings -> Bindings)
liftInput (Value _) = return id
liftInput (Variable x tau) =
  do sx <- fresh x tau
     return (bind x sx)
liftInput (PConstructor _ ps _) =
  do foldrM (\p bs' -> do b <- liftInput p
                          return (bs' . b)
            ) id ps
liftInput (List ps _) =
  do foldrM (\p bs' -> do b <- liftInput p
                          return (bs' . b)
            ) id ps

liftLambdaInputs :: Term Type -> Formula (Term Type, Bindings -> Bindings)
liftLambdaInputs (Lambda p t _) =
  do bs <- liftInput p
     return (t, bs)
liftLambdaInputs t = return (t, id)


-- Constraint generation
translate :: Term Type -> Formula SValue
translate (Pattern    p) = translatePattern p
translate (Lambda p t _) =
  do bs <- liftInput p
     local bs $ translate t
translate (Application t1 t2 _) =
  do t2'        <- translate t2
     (bs, body) <- functionUnify t1 t2'
     local bs $ translate body
translate (Let p t1 t2 _) =
  do t1' <- translate t1
     bs  <- symUnify p t1'
     local bs $ translate t2
translate (Case t0 ts _) =
  do sp      <- translate t0
     (bs, t) <- firstMatch sp ts
     local bs $ translate t
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
translatePattern (List ps _) =
  do sps <- mapM translatePattern ps
     return $ SList sps

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
numeric sv          = error  $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error  $ "Expected a boolean symval, but got " ++ show sv

-- branches :: SValue -> [(SValue, SValue)] -> SValue
-- branches _ [] = error "Non-exhaustive patterns in case statement"
-- branches v ((p, t) : rest) =
--   merge (unifyAndLift v p) (substituteIn t v p) $ branches v rest

