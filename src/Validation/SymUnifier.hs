module Validation.SymUnifier where

import Core.Syntax
import Validation.Formula

import Data.Foldable (foldrM)


-- Abbreviations
type SymUnificationError = String
type Transformation      = (Bindings -> Bindings)

data PatternMatch a =
    NoMatch SymUnificationError
  | MatchBy a

type Unifier = Either String Transformation


-- SValue unification
symUnify :: Pattern a -> SValue -> Formula Transformation
symUnify p sv =
  case unify p sv of
    Right bs -> return bs
    Left err -> error err


-- Unify a regular pattern against a symbolic value and return the new bindings
unify :: Pattern a -> SValue -> Unifier
unify (Value             _) _            = Right id
unify (Variable     x    _) sx           = Right $ bind x sx
unify (List           ps _) (SList  svs) = unifyMany $ zip ps svs
unify (PConstructor c ps _) (SCtr d svs)
  | c == d    = unifyMany $ zip ps svs
  | otherwise = Left $
    "Type mismatch occurred when trying to unify\n\
    \pattern with constructor '" ++ c ++
    "' against symbolic value with constructor '" ++ d ++ "'"
unify p sv = Left $
  "Unexpected type error occurred\n\
  \trying to unify concrete pattern '"
  ++ show p  ++ "' against symbolic value '"
  ++ show sv ++ "'"

unifyMany :: [(Pattern a, SValue)] -> Unifier
unifyMany =
  foldrM (\(p, sv) bs -> case unify p sv of
                           Right  b -> Right (bs . b)
                           Left err -> Left err
         ) id


-- Unify the function's input pattern against the symbolic argument
-- If there's a match, return the bindings and the body so we can translate
-- the body wrt. the new bindings
functionUnify :: Term a -> SValue -> Formula (Transformation, Term a)
functionUnify (Lambda p t1 _) sv =
  case unify p sv of
    Right bs  -> return (bs, t1)
    Left  err -> error err
functionUnify t1 t2 = error $ "Error when translating the application of term '"
                           ++ show t1 ++ "' to symbolic value '" ++ show t2
                           ++ "'\n'" ++ show t1 ++ "' is not a function."


-- Find the first match between a (symbolic) selector value and concrete patterns
-- in a series of case branches
firstMatch :: SValue -> [(Pattern a, Term a)] -> Formula (Transformation, Term a)
firstMatch sv [] = error $ "Non-exhaustive patterns in case statement - "
                        ++ "no match for '" ++ show sv ++ "'"
firstMatch sv ((p, t) : rest) =
  case unify p sv of
    Right bs -> return (bs, t)
    Left  _  -> firstMatch sv rest
