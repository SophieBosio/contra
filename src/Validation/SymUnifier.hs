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

module Validation.SymUnifier where

import Core.Syntax
import Validation.Formula

import Data.List     (intercalate)


-- Abbreviations
type SymUnificationErrors = [String]
type ErrorMessage         = String
type Transformation       = (Bindings -> Bindings)

data PatternMatch =
    MatchBy Transformation
  | NoMatch ErrorMessage

type Unifier = Either SymUnificationErrors Transformation

newtype Substitution = Substitution { unifier :: Unifier }


-- Subsitution is a (hacky) semigroup and a monoid.
-- The semigroup instance for Either forgets information,
-- so we can't use that directly.
instance Semigroup Substitution where
  s <> s' = Substitution $
    case unifier s of
      Right  u ->
        case unifier s' of
          Left err -> Left err
          Right u' -> Right $ u' . u
      Left err ->
        case unifier s' of
          Left err' -> Left $ err <> err'
          Right   _ -> Left err

instance Monoid Substitution where
  mempty  = Substitution $ Right id
  mappend = (<>)

substError :: String -> Substitution
substError = Substitution . Left . return

substitution :: Transformation -> Substitution
substitution = Substitution . Right


-- Export
symUnify :: Pattern Type -> SValue -> PatternMatch
symUnify p sv =
  case unifier $ sUnify p sv of
       Right bs -> MatchBy bs
       Left err -> NoMatch $ intercalate "\n" err

sUnify :: Pattern Type -> SValue -> Substitution
sUnify (Value             _) _            = mempty
sUnify (Variable     x    _) sv           = substitution $ bind x sv
sUnify (List           ps _) (SArgs  svs) =
  foldr (\(p, sv) u -> u <> sUnify p sv) mempty $ zip ps svs
sUnify (PConstructor c ps (ADT t)) (SCtr d _ svs)
  | t == d     = foldr (\(p, sv) u -> u <> sUnify p sv) mempty $ zip ps svs
  | otherwise  = substError $
    "Unexpected type occurred when trying to unify\n\
    \concrete pattern with constructor '" ++ c ++ "' and type '" ++ show t
    ++ "' against symbolic value of type '" ++ d ++ "'"
sUnify p sv = substError $
  "Unexpected type error occurred\n\
  \trying to unify concrete pattern '"
  ++ show p  ++ "' against symbolic value '"
  ++ show sv ++ "'"
