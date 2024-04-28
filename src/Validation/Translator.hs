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

import Data.Foldable (foldrM)
import Data.Hashable (hash)
import Data.SBV


-- Recursion depth for ADTs
defaultRecDepth :: RecursionDepth
defaultRecDepth = 20


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
     (bs, body) <- unifyAndBind t1 t2'
     local bs $ translate body
translate (Lambda p t _) =
  do bs <- liftPattern p
     local bs $ translate t
translate (Let p t1 t2 _) =
  do t1' <- translate t1
     bs  <- unifyOrFail p t1'
     local bs $ translate t2
translate (Case t0 ts _) =
  do sp      <- translate t0
     translateBranches sp ts
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

translateBranches :: SValue -> [(Pattern Type, Term Type)] -> Formula SValue
translateBranches _  [] = error "Non-exhaustive patterns in case statement."
translateBranches sv [(alt, body)] =
  case symUnify alt sv of
    NoMatch _  -> translateBranches sv []
    MatchBy bs -> local bs $ translate body
translateBranches sv ((alt, body) : rest) =
  case symUnify alt sv of
    NoMatch _  -> translateBranches sv rest
    MatchBy bs -> do alt' <- local bs $ translatePattern alt
                     let cond = truthy $ sEqual alt' sv
                     body' <- local bs $ translate body
                     next  <- translateBranches sv rest
                     return $ merge cond body' next


-- Create symbolic input variables
emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")

liftPattern :: Pattern Type -> Formula (Bindings -> Bindings)
liftPattern (Value _) = return id
liftPattern (Variable x tau) =
  do sx <- createSymbolic defaultRecDepth (Variable x tau)
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
     return (bs, t)
liftPropertyInputPatterns t = return (id, t)


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
-- createSymbolic 0     (Variable x (ADT adt)) =
--   do env  <- environment
--      ctrs <- constructors env adt
--      case removeRecursiveCtrs ctrs of
--        []    -> error $
--          "Fatal: Maxed out recursion depth when creating symbolic ADT '"
--          ++ show adt ++ "'"
--        ctrs' -> do (si, sFields) <- symFields 0 adt ctrs'
--                    return $ SCtr adt si sFields
-- createSymbolic depth (Variable x (ADT adt)) =
--   do env  <- environment
--      ctrs <- constructors env adt
--      (si, sFields) <- symFields (depth - 1) adt ctrs
--      return $ SCtr adt si sFields
createSymbolic _ p = error $
     "Unexpected request to create symbolic sub-pattern '"
  ++ show p ++ "' of type '" ++ show (annotation p) ++ "'"
  ++ "\nPlease note that generating arbitrary functions is not supported."


-- * Helpers for creating symbolic ADT variables
symFields :: RecursionDepth -> D -> [Constructor] -> Formula (SInteger, [SValue])
symFields depth adt ctrs =
  do si <- lift $ sInteger "selector"
     let cardinality = literal $ toInteger $ length ctrs
     lift $ constrain $
       (si .>= 0) .&& (si .< cardinality)
     types <- symSelect si adt ctrs
     let names = zipWith (\tau i -> show (hash (adt ++ show tau)) ++ show i)
                 types
                 ([0..] :: [Integer])
     let fields = zipWith Variable names types
     sFields <- mapM (createSymbolic depth) fields
     return (si, sFields)

symSelect :: SInteger -> D -> [Constructor] -> Formula [Type]
symSelect _  adt [   ] = error $ "Fatal: Failed to create symbolic variable for ADT '"
                        ++ show adt ++ "'"
symSelect si adt [ctr] =
  do env <- environment
     i   <- selector env adt (nameOf ctr)
     return $ ite (si .== literal i)
                  (fieldsOf ctr)
                  (error $ "Fatal: Failed to create input variable for ADT '"
                        ++ show adt ++ "'")
symSelect si adt (ctr : ctrs) =
  do env  <- environment
     i    <- selector env adt (nameOf ctr)
     next <- symSelect si adt ctrs
     return $ ite (si .== literal i)
                  (fieldsOf ctr)
                  next
 
nameOf :: Constructor -> C
nameOf (Constructor c _) = c

fieldsOf :: Constructor -> [Type]
fieldsOf (Constructor _ taus) = taus

removeRecursiveCtrs :: [Constructor] -> [Constructor]
removeRecursiveCtrs = filter nonRecursive
  where
    nonRecursive ctr = all nonAlgebraic $ fieldsOf ctr
    nonAlgebraic (ADT _) = False
    nonAlgebraic _          = True
    

-- Symbolic "unification" and unification constraint generation
unifyOrFail :: Pattern Type -> SValue -> Formula Transformation
unifyOrFail p sv =
  case symUnify p sv of
    MatchBy  bs -> return bs
    NoMatch err -> error err

unifyAndBind :: Term Type -> SValue -> Formula (Transformation, Term Type)
-- A function is either a Lambda that can be applied directly
-- or it's an Application that will (eventually) return a Lambda.
-- Applying a Lambda symbolically means unifying the input pattern against the
-- symbolic argument and binding the free variables from the input accordingly.
unifyAndBind (Lambda p t1 _) sv =
  do bs <- unifyOrFail p sv
     return (bs, t1)
unifyAndBind (Application t1 t2 _) sv =
  do t2'         <- translate t2
     (bs,  f   ) <- unifyAndBind t1 t2'
     (bs', body) <- unifyAndBind f sv
     return (bs' . bs, body)
unifyAndBind t1 t2 = error $ "Error when translating the application of term '"
                           ++ show t1 ++ "' to symbolic value '" ++ show t2
                           ++ "'\n'" ++ show t1 ++ "' is not a function."


-- Translation helpers
numeric :: SValue -> Formula SInteger
numeric (SNumber n) = return n
numeric sv          = error  $ "Expected a numeric symval, but got " ++ show sv

boolean :: SValue -> Formula SBool
boolean (SBoolean b) = return b
boolean sv           = error  $ "Expected a boolean symval, but got " ++ show sv

symSelector :: Type -> C -> Formula SInteger
symSelector (ADT t) c =
  do env <- environment
     sel <- selector env t c
     let si = literal sel
     return si
symSelector tau c = error $ "Type error: Constructor '" ++ show c ++
                            "' typed with non-ADT type '" ++ show tau ++ "'"
