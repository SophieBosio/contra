module Validation.Translator where

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

import Core.Syntax
import Environment.ERSymbolic
import Validation.Formula
import Validation.SymUnifier

import Data.Foldable (foldrM)
import Data.Hashable (hash)
import Data.SBV


-- Export
translateToFormula :: Term Type -> Formula SValue
translateToFormula prop =
  do (bs, prop') <- liftPropertyInputPatterns prop
     local bs $ translate prop'


-- Constraint generation
translate :: Term Type -> Formula SValue
translate (Pattern    p) = translatePattern p
translate (Application t1 t2 _) =
  do t2'        <- translate t2
     (bs, body) <- functionUnify t1 t2'
     local bs $ translate body
translate (Lambda p t _) =
  do bs <- liftPattern p
     local bs $ translate t
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
     return $ SArgs sps

translateValue :: Value a -> Formula SValue
translateValue (Unit      _) = return SUnit
translateValue (Number  n _) = return $ SNumber  $ literal n
translateValue (Boolean b _) = return $ SBoolean $ literal b
translateValue (VConstructor c vs _) =
  do svs <- mapM translateValue vs
     return $ SCtr c svs


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftPattern :: Pattern Type -> Formula (Bindings -> Bindings)
liftPattern (Value _) = return id
liftPattern (Variable x tau) =
  do sx <- createSymbolic (Variable x tau)
     return (bind x sx)
liftPattern (PConstructor _ ps _) =
  do foldrM (\p bs' -> do b <- liftPattern p
                          return (bs' . b)
            ) id ps
liftPattern (List ps _) =
  do foldrM (\p bs' -> do b <- liftPattern p
                          return (bs' . b)
            ) id ps

liftPropertyInputPatterns :: Term Type -> Formula (Bindings -> Bindings, Term Type)
liftPropertyInputPatterns (Lambda p t _) =
  do bs <- liftPattern p
     return (bs, t)
liftPropertyInputPatterns t = return (id, t)


-- Create symbolic variables
createSymbolic :: Pattern Type -> Formula SValue
createSymbolic (Variable _ Unit')    = return SUnit
createSymbolic (Variable x Integer') =
  do sx <- liftSymbolic $ sInteger x
     return $ SNumber sx
createSymbolic (Variable x Boolean') =
  do sx <- liftSymbolic $ sBool x
     return $ SBoolean sx
createSymbolic (Variable x (Variable' _)) =
  do sx <- liftSymbolic $ free x
     return $ SNumber sx
createSymbolic (Variable _ (TypeList [])) =
  do return $ SArgs []
createSymbolic (Variable x (TypeList ts)) =
     -- Fabricate new name for each variable by hashing <x><type-name>
     -- and appending the index of the variable type in the TypeList
  do let names = zipWith (\s i -> show (hash (x ++ show s)) ++ show i)
                 ts
                 [0..(length ts)]
     let ps    = zipWith Variable names ts
     sxs <- mapM createSymbolic ps
     return $ SArgs sxs
-- TODO: Create symbolic variables for functions
-- createSymbolic (Variable x (t1 :->: t2)) = undefined
-- -- You have the name of the function and the program env
-- TODO: Create symbolic variables for ADTs
-- createSymbolic (Variable x (ADT t)) = undefined
-- To generate a random ADT, you could enumerate its constructors with an index
createSymbolic p = error $ "Unexpected request to create symbolic sub-pattern '"
                        ++ show p ++ "' of type '" ++ show (annotation p) ++ "'"



-- Translation helpers
numeric :: SValue -> Formula SInteger
numeric (SNumber n) = return n
numeric sv          = error  $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error  $ "Expected a boolean symval, but got " ++ show sv

-- Unify the function's input pattern against the symbolic argument
-- If there's a match, return the bindings and the body so we can translate
-- the body wrt. the new bindings
functionUnify :: Term Type -> SValue -> Formula (Transformation, Term Type)
functionUnify (Lambda p t1 _) sv =
  case sUnify p sv of
    Right bs  -> return (bs, t1)
    Left  err -> error err
functionUnify (Application t1 t2 _) sv =
  do t2'         <- translate t2
     (bs,  f   ) <- functionUnify t1 t2'
     (bs', body) <- functionUnify f sv
     return (bs' . bs, body)
functionUnify t1 t2 = error $ "Error when translating the application of term '"
                           ++ show t1 ++ "' to symbolic value '" ++ show t2
                           ++ "'\n'" ++ show t1 ++ "' is not a function."
