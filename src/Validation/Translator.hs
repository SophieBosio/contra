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
   * 'createSymbolic'

  'translateFormula' takes a property (as a Contra term) and translates it into
  a symbolic term, represented by SValues, which in turn hold symbolic variables.

  It uses the Formula monad, defined in Validation.Formula.

  It first lifts all the input variables of the property into the Formula monad
  (and consequently into the Symbolic monad). After partial evaluation of the
  property in the context of the program, these *should* be all the input that
  the SMT solver has to generate for us. Then it translates the rest of the
  term, which is the property body.

  The function 'liftPropertyInputPatterns' is responsible for lifting all the
  property's input patterns. It, in turn, calls 'createSymbolic', translates
  each input variable to its SValue equivalent and binds them, by using the
  underlying Symbolic monad to create symbolic variables.

-}

module Validation.Translator where

import Core.Syntax
import Environment.Environment
import Environment.ERSymbolic
import Validation.Formula
import Validation.SymUnifier

import Data.SBV
import Data.Foldable (foldrM)
import Data.Hashable (hash)


-- Export
translateToFormula :: RecursionDepth -> Term Type -> Formula SValue
translateToFormula depth prop =
  do (bs, prop') <- liftPropertyInputPatterns depth prop
     local bs $ translate depth prop'


-- Constraint generation
translate :: RecursionDepth -> Term Type -> Formula SValue
translate depth (Pattern    p) = translatePattern depth p
translate depth (Application t1 t2 _) =
  do t2'        <- translate depth t2
     (bs, body) <- unifyAndBind depth t1 t2'
     local bs $ translate depth body
translate depth (Lambda p t _) =
  do bs <- liftPattern depth p
     local bs $ translate depth t
translate depth (Let p t1 t2 _) =
  do t1' <- translate depth t1
     bs  <- unifyOrFail p t1'
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

translatePattern :: RecursionDepth -> Pattern Type -> Formula SValue
translatePattern _ (Value v) = translateValue v
-- All input variables are bound at this point,
-- so if a variable is not a function and not in the bindings, that's an error
translatePattern depth (Variable x _) =
  do env <- environment
     case map snd $ filter ((== x) . fst) (envFunctions env ++ envProperties env) of
       [ t@(Lambda {}) ] -> translate depth t
       [ ] -> do bindings <- ask
                 return $ bindings x
       _   -> error $ "Variable '" ++ x ++ "' is not a function and not bound"
translatePattern depth (PConstructor c ps (ADT d)) =
  do sps <- mapM (translatePattern depth) ps
     return $ SCtr d c sps
translatePattern depth (List ps _) =
  do sps <- mapM (translatePattern depth) ps
     return $ SArgs sps
translatePattern _ p@(PConstructor {}) = error
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
  case symUnify alt sv of
    NoMatch _  -> translateBranches depth sv []
    MatchBy bs -> local bs $ translate depth body
translateBranches depth sv ((alt, body) : rest) =
  case symUnify alt sv of
    NoMatch _  -> translateBranches depth sv rest
    MatchBy bs -> do alt' <- local bs $ translatePattern depth alt
                     cond <- alt' `sEqual` sv
                     body' <- local bs $ translate depth body
                     next  <- translateBranches depth sv rest
                     return $ merge (truthy cond) body' next


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftPattern :: RecursionDepth -> Pattern Type -> Formula (Bindings -> Bindings)
liftPattern _ (Value _) = return id
liftPattern depth (Variable x tau) =
  do sx <- createSymbolic depth (Variable x tau)
     return (bind x sx)
liftPattern depth (PConstructor _ ps _) =
  do foldrM (\p bs -> do b <- liftPattern depth p
                         return (bs . b)
            ) id ps
liftPattern depth (List ps _) =
  do foldrM (\p bs -> do b <- liftPattern depth p
                         return (bs . b)
            ) id ps

liftPropertyInputPatterns :: RecursionDepth -> Term Type
                          -> Formula (Bindings -> Bindings, Term Type)
liftPropertyInputPatterns depth (Lambda p t _) =
  do bs <- liftPattern depth p
     return (bs, t)
liftPropertyInputPatterns _ t = return (id, t)


-- Create symbolic variables for SBV to instantiate during solving
createSymbolic :: RecursionDepth -> Pattern Type -> Formula SValue
createSymbolic _ (Variable _ Unit')    = return SUnit
createSymbolic _ (Variable x Integer') =
  do sx <- lift $ sInteger x
     return $ SNumber sx
createSymbolic _ (Variable x Boolean') =
  do sx <- lift $ sBool x
     return $ SBoolean sx
createSymbolic _ (Variable x (Variable' _)) =
  do sx <- lift $ free x
     return $ SNumber sx
createSymbolic _ (Variable _ (TypeList [])) =
  do return $ SArgs []
createSymbolic depth (Variable x (TypeList ts)) =
     -- We should never be asked to create input for this type, since it's
     -- interal and not exposed to the user. However, we are able to do so.
     -- Fabricate new name for each variable by hashing <x><type-name>
     -- and appending the index of the variable type in the TypeList.
  do let names = zipWith (\tau i -> show (hash (x ++ show tau)) ++ show i)
                 ts
                 ([0..] :: [Integer])
     let ps    = zipWith Variable names ts
     sxs <- mapM (createSymbolic depth) ps
     return $ SArgs sxs
createSymbolic 0     (Variable x (ADT adt)) = error $
  "Reached max. recursion depth while trying to generate symbolic ADT "
  ++ adt ++ "' for variable '" ++ x ++ "'"
createSymbolic depth (Variable x (ADT adt)) =
  do env  <- environment
     ctrs <- constructors env adt
     si   <- createSelector ctrs
     sCtr <- selectConstructor (depth - 1) adt si ctrs
     desc <- lift $ sString x
     lift $ constrain $ desc .== literal (show sCtr)
     return sCtr
createSymbolic _ p = error $
     "Unexpected request to create symbolic sub-pattern '"
  ++ show p ++ "' of type '" ++ show (annotation p) ++ "'"
  ++ "\nPlease note that generating arbitrary functions is not supported."


-- * Helpers for creating symbolic ADT variables
createSelector :: [Constructor] -> Formula SInteger
createSelector ctrs =
  do si <- lift sInteger_
     let cardinality = literal $ toInteger $ length ctrs
     lift $ constrain $
       (si .>= 0) .&& (si .< cardinality)
     return si

selectConstructor :: RecursionDepth -> D -> SInteger -> [Constructor]
                  -> Formula SValue
selectConstructor 0     d _  _  = error $
  "Reached max. recursion depth while trying to \
  \create symbolic variable for ADT '" ++ d ++ "'"
selectConstructor _     d _  [] = error $
  "Fatal: Failed to create symbolic variable for ADT '" ++ d ++ "'"
selectConstructor depth d _  [Constructor c types] =
  do let names = zipWith (\tau i -> show (hash (d ++ show tau)) ++ show i)
                 types
                 ([0..] :: [Integer])
     let fields = zipWith Variable names types
     sFields <- mapM (createSymbolic depth) fields
     return $ SCtr d c sFields
selectConstructor depth d si ((Constructor c types) : ctrs) =
  do env   <- environment
     sel   <- selector env d c
     let names = zipWith (\tau i -> show (hash (d ++ show tau)) ++ show i)
                 types
                 ([0..] :: [Integer])
     let fields = zipWith Variable names types
     sFields <- mapM (createSymbolic depth) fields
     next  <- selectConstructor depth d si ctrs
     return $ merge (si .== literal sel) (SCtr d c sFields) next


-- Symbolic "unification" and unification constraint generation
unifyOrFail :: Pattern Type -> SValue -> Formula Transformation
unifyOrFail p sv =
  case symUnify p sv of
    MatchBy  bs -> return bs
    NoMatch err -> error err

unifyAndBind :: RecursionDepth -> Term Type -> SValue
             -> Formula (Transformation, Term Type)
-- A function is either a Lambda that can be applied directly
-- or it's an Application that will (eventually) return a Lambda.
-- Applying a Lambda symbolically means unifying the input pattern against the
-- symbolic argument and binding the free variables from the input accordingly.
unifyAndBind 0 t s = error $
  "Reached max. recursion depth while trying to translate function application\
  \symbolically.\nCurrent step: Applying '" ++ show t ++ "' to '" ++ show s ++ "'"
unifyAndBind _ (Lambda p t1 _) sv =
  do bs <- unifyOrFail p sv
     return (bs, t1)
unifyAndBind depth (Application t1 t2 _) sv =
  do t2'         <- translate depth t2
     (bs,  f   ) <- unifyAndBind (depth - 1) t1 t2'
     (bs', body) <- unifyAndBind (depth - 1) f sv
     return (bs' . bs, body)
unifyAndBind depth (Pattern (Variable x _)) sv =
  do env <- environment
     case map snd $ filter ((== x) . fst) (envFunctions env ++ envProperties env) of
       [f] -> unifyAndBind depth f sv
       [ ] -> error $ "Error when translating the application of terms.\n\
                          \Variable with name '" ++ x ++ "' is not a function."
       _   -> error $ "Ambiguous bindings for variable '" ++ x ++ "'"
unifyAndBind _ t1 t2 = error $ "Error when translating the application of term '"
                           ++ show t1 ++ "' to symbolic value '" ++ show t2
                           ++ "'\n'" ++ show t1 ++ "' is not a function."


-- Translation helpers
numeric :: SValue -> Formula SInteger
numeric (SNumber n) = return n
numeric sv          = error  $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error  $ "Expected a boolean symval, but got " ++ show sv
