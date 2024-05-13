{-

  Module      : Validation.Translator
  Description : Symbolic formula translator for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  The Translator is responsible for translating Contra terms into SBV formulae,
  by translating them to intermediary SValue formulae.

  Its main functions are:
   * 'translateFormula'
   * 'translate'
   * 'liftPattern'

  'translateFormula' takes a property (as a Contra term) and translates it into
  a symbolic term, represented by SValues, which in turn hold symbolic variables.

  It uses the Formula monad, defined in Validation.Formula.

  It first lifts all the input variables of the property into the Formula monad
  (and consequently into the Symbolic monad). After partial evaluation of the
  property in the context of the program, these *should* be all the input that
  the SMT solver has to generate for us. Then it translates the rest of the
  term, which is the property body.

  The function 'liftPropertyInputPatterns' is responsible for lifting all the
  property's input patterns. It, in turn, calls 'createSymbolic' from Formula,
  translates each input variable to its SValue equivalent and binds them,
  by using the underlying Symbolic monad to create symbolic variables.

-}

{-# LANGUAGE LambdaCase #-}

module Validation.Translator where

import Core.Syntax
import Environment.Environment
import Environment.ERSymbolic
import Validation.Formula
import Validation.SymbolicUnification

import Data.SBV
import Data.Foldable (foldrM)


-- * Export
translateToFormula :: RecursionDepth -> Term Type -> Formula SValue
translateToFormula depth prop =
  do (bs, prop') <- liftPropertyInputPatterns prop
     local bs $ translate depth prop'


-- * Constraint generation
translate :: RecursionDepth -> Term Type -> Formula SValue
translate 0 t = error $
  "Reached max. recursion depth while trying to translate term '" ++ show t ++ "'"
translate _     (Pattern    p) = translatePattern p
translate depth (Application t1 t2 _) =
  do t2'        <- translate depth t2
     (bs, body) <- unifyAndBind depth t1 t2'
     local bs $ translate (depth - 1) body
translate depth (Lambda p t _) =
  do bs <- liftPattern p
     local bs $ translate (depth - 1) t
translate depth (Let p t1 t2 _) =
  do t1' <- translate depth t1
     bs  <- symbolicallyUnify p t1'
     local bs $ translate depth t2
translate depth (Case t0 ts _) =
  do sp <- translate depth t0
     translateBranches depth sp ts
translate depth (TConstructor c ts (ADT d)) =
  do sts <- mapM (translate depth) ts
     return $ SCtr d c sts
translate depth (Plus t0 t1 _) =
  do t0' <- translate depth t0 >>= numeric
     t1' <- translate depth t1 >>= numeric
     return $ SNumber $ t0' + t1'
translate depth (Minus t0 t1 _) =
  do t0' <- translate depth t0>>= numeric
     t1' <- translate depth t1>>= numeric
     return $ SNumber $ t0' - t1'
translate depth (Lt t0 t1 _) =
  do t0' <- translate depth t0 >>= numeric
     t1' <- translate depth t1 >>= numeric
     return $ SBoolean $ t0' .< t1'
translate depth (Gt t0 t1 _) =
  do t0' <- translate depth t0 >>= numeric
     t1' <- translate depth t1 >>= numeric
     return $ SBoolean $ t0' .> t1'
translate depth (Equal t0 t1 _) =
  do t0' <- translate depth t0
     t1' <- translate depth t1
     t0' `sEqual` t1'
translate depth (Not t0 _) =
  do t0' <- translate depth t0 >>= boolean
     return $ SBoolean $ sNot t0'
translate _ t@(TConstructor {}) = error
  $ "Ill-typed constructor argument '" ++ show t ++ "'"

translatePattern :: Pattern Type -> Formula SValue
translatePattern (Value v) = translateValue v
-- All input variables are bound at this point,
-- so if a variable is not a function and not in the bindings, that's an error
translatePattern (Variable x _) =
  do env <- environment
     case map snd $ filter ((== x) . fst) (envFunctions env ++ envProperties env) of
       [ ] -> do bindings <- ask
                 return $ bindings x
       _   -> error $ "Variable '" ++ x ++ "' is unbound"
translatePattern (PConstructor c ps (ADT d)) =
  do sps <- mapM translatePattern ps
     return $ SCtr d c sps
translatePattern (List ps _) =
  do sps <- mapM translatePattern ps
     return $ SArgs sps
translatePattern p@(PConstructor {}) = error
  $ "Ill-typed constructor argument '" ++ show p ++ "'"

translateValue :: Value Type -> Formula SValue
translateValue (Unit      _) = return SUnit
translateValue (Number  n _) = return $ SNumber  $ literal n
translateValue (Boolean b _) = return $ SBoolean $ literal b
translateValue (VConstructor c vs (ADT d)) =
  do svs <- mapM translateValue vs
     return $ SCtr d c svs
translateValue v@(VConstructor {}) = error
  $ "Ill-typed constructor argument '" ++ show v ++ "'"

translateBranches :: RecursionDepth
                  -> SValue -> [(Pattern Type, Term Type)]
                  -> Formula SValue
translateBranches _  _ [] = error "Non-exhaustive patterns in case statement."
translateBranches depth sv [(alt, body)] =
  if unifiable alt sv
    then do bs <- symbolicallyUnify alt sv
            local bs $ translate depth body
    else translateBranches depth sv []
translateBranches depth sv ((alt, body) : rest) =
  if unifiable alt sv
    then do bs    <- symbolicallyUnify alt sv
            alt'  <- local bs $ translatePattern alt
            cond  <- alt' `sEqual` sv
            body' <- local bs $ translate depth body
            next  <- translateBranches depth sv rest
            return $ merge (truthy cond) body' next
    else translateBranches depth sv rest


-- * Lift symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftPattern :: Pattern Type -> Formula (Bindings -> Bindings)
liftPattern (Value _) = return id
liftPattern (Variable x tau) =
  do sx <- createSymbolic (Variable x tau)
     return (bind x sx)
liftPattern (PConstructor _ ps _) =
  do foldrM (\p bs -> do b <- liftPattern p
                         return (bs . b)
            ) id ps
liftPattern (List ps _) =
  do foldrM (\p bs -> do b <- liftPattern p
                         return (bs . b)
            ) id ps

liftPropertyInputPatterns :: Term Type -> Formula (Bindings -> Bindings, Term Type)
liftPropertyInputPatterns (Lambda p t _) =
  do bs <- liftPattern p
     (bs', t') <- liftPropertyInputPatterns t
     return (bs' . bs, t')
liftPropertyInputPatterns t = return (id, t)


-- * Symbolic "unification" and unification constraint generation
symbolicallyUnify :: Pattern Type -> SValue -> Formula Transformation
symbolicallyUnify p sv =
  symUnify p sv >>= \case
    MatchBy  bs -> return bs
    NoMatch err -> error err

unifyAndBind :: RecursionDepth -> Term Type -> SValue
             -> Formula (Transformation, Term Type)
-- A function is either a Lambda that can be applied directly
-- or it's an variable or Application that will (eventually) return a Lambda.
-- Applying a Lambda symbolically means unifying the input pattern against the
-- symbolic argument and binding the free variables from the input accordingly.
unifyAndBind 0 t s = error $
  "Reached max. recursion depth while trying to translate function application \
  \symbolically.\nCurrent step: Applying '" ++ show t ++ "' to '" ++ show s ++ "'"
unifyAndBind depth (Pattern (Variable x _)) sv =
  do env <- environment
     case map snd $ filter ((== x) . fst) (envFunctions env ++ envProperties env) of
       [ Lambda p t a ] -> unifyAndBind depth (Lambda p t a) sv
       _                -> error $
         "Variable '" ++ x ++ "' is not a function or not bound"
unifyAndBind _ (Lambda p t _) sv =
  do bs <- symbolicallyUnify p sv
     return (bs, t)
unifyAndBind depth (Application t1 t2 _) sv =
  do t2'         <- translate depth t2
     (bs,  f   ) <- unifyAndBind (depth - 1) t1 t2'
     (bs', body) <- unifyAndBind (depth - 1) f sv
     return (bs' . bs, body)
unifyAndBind _ t1 t2 = error $ "Error when translating the application of term '"
                           ++ show t1 ++ "' to symbolic value '" ++ show t2
                           ++ "'\n'" ++ show t1 ++ "' is not a function."


-- * Translation helpers
numeric :: SValue -> Formula SInteger
numeric (SNumber n) = return n
numeric sv          = error  $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error  $ "Expected a boolean symval, but got " ++ show sv
