module Validation.SymUnifier where

import Core.Syntax
import Validation.Formula

import Data.Foldable (foldrM)
import Data.SBV

-- SValue Unification
-- Unify a regular pattern against a symbolic value and return the new bindings
unifyAndLift :: Pattern a -> SValue -> Formula (Bindings -> Bindings)
unifyAndLift (Value             _) _            = return id
unifyAndLift (Variable     x    _) sx           = return $ bind x sx
unifyAndLift (List           ps _) (SList  svs) = unifyAndLiftMany $ zip ps svs
unifyAndLift (PConstructor c ps _) (SCtr d svs)
  | c == d = unifyAndLiftMany $ zip ps svs
  | otherwise = error $
    "Type mismatch occurred when trying to unify\n\
    \pattern with constructor '" ++ c ++
    "' against symbolic value with constructor '" ++ d ++ "'"
unifyAndLift p sv = error $
  "Unexpected type error occurred\n\
  \trying to unify concrete pattern '"
  ++ show p  ++ "' against symbolic value '"
  ++ show sv ++ "'"

unifyAndLiftMany :: [(Pattern a, SValue)] -> Formula (Bindings -> Bindings)
unifyAndLiftMany =
  foldrM (\(p, sv) bs -> do b <- unifyAndLift p sv
                            return (bs . b)
         ) id

-- Unify the function's input pattern against the symbolic argument
-- If there's a match, return the bindings and the body so we can translate
-- the body wrt. the new bindings
functionUnify :: Term a -> SValue -> Formula (Bindings -> Bindings, Term a)
functionUnify (Lambda p t1 _) sv =
  do bs <- unifyAndLift p sv
     return (bs, t1)
functionUnify t1 t2 = error $ "Error when translating the application of term '"
                           ++ show t1 ++ "' to symbolic value '" ++ show t2
                           ++ "'\n'" ++ show t1 ++ "' is not a function."

