module Validation.SymUnifier where

{-

  Module      : Validation.SymUnifier
  Description : Symbolic unification algorithm for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  SymUnifier acts as a pseudo-mapping between Patterns and SValues, allowing
  us to "unify" them - e.g., in Case-statements, Let-Statements and Lambdas.

-}

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
  case sUnify p sv of
    Right bs -> return bs
    Left err -> error err


-- Unify a regular pattern against a symbolic value and return the new bindings
sUnify :: Pattern a -> SValue -> Unifier
sUnify (Value             _) _            = Right id
sUnify (Variable     x    _) sx           = Right $ bind x sx
sUnify (List           ps _) (SList  svs) = sUnifyMany $ zip ps svs
sUnify (PConstructor c ps _) (SCtr d svs)
  | c == d    = sUnifyMany $ zip ps svs
  | otherwise = Left $
    "Type mismatch occurred when trying to unify\n\
    \pattern with constructor '" ++ c ++
    "' against symbolic value with constructor '" ++ d ++ "'"
sUnify p sv = Left $
  "Unexpected type error occurred\n\
  \trying to unify concrete pattern '"
  ++ show p  ++ "' against symbolic value '"
  ++ show sv ++ "'"

sUnifyMany :: [(Pattern a, SValue)] -> Unifier
sUnifyMany =
  foldrM (\(p, sv) bs -> case sUnify p sv of
                           Right  b -> Right (bs . b)
                           Left err -> Left err
         ) id


-- Find the first match between a (symbolic) selector value and concrete patterns
-- in a series of case branches on the form [(Pattern a, Term a)]
firstMatch :: SValue -> [(Pattern a, Term a)] -> Formula (Transformation, Term a)
firstMatch sv [] = error $ "Non-exhaustive patterns in case statement - "
                        ++ "no match for '" ++ show sv ++ "'"
firstMatch sv ((p, t) : rest) =
  case sUnify p sv of
    Right bs -> return (bs, t)
    Left  _  -> firstMatch sv rest
