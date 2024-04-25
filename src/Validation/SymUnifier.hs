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

import Data.List     (intercalate)


-- Abbreviations
type SymUnificationError = [String]
type Transformation      = (Bindings -> Bindings)

data PatternMatch =
    NoMatch SymUnificationError
  | MatchBy Transformation

type Unifier = Either SymUnificationError Transformation

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
symUnify :: Pattern a -> SValue -> Formula Transformation
symUnify p sv =
  case unifier $ sUnify p sv of
       Right bs -> return bs
       Left err -> error $ intercalate "\n" err

firstMatch :: SValue -> [(Pattern a, Term a)] -> (Transformation, Term a)
firstMatch sv [] = error $ "Non-exhaustive patterns in case statement - "
                        ++ "no match for '" ++ show sv ++ "'"
firstMatch sv ((p, t) : rest) =
  case unifier $ sUnify p sv of
    Right bs -> (bs, t)
    Left  _  -> firstMatch sv rest


-- Main functions
sUnify :: Pattern a -> SValue -> Substitution
sUnify (Value             _) _            = mempty
sUnify (Variable     x    _) sv           = substitution $ bind x sv
sUnify (List           ps _) (SArgs  svs) = sUnifyMany $ zip ps svs
sUnify (PConstructor c ps _) (SCtr d svs)
  | c == d    = sUnifyMany $ zip ps svs
  | otherwise = substError $
    "Type mismatch occurred when trying to unify\n\
    \pattern with constructor '" ++ c ++
    "' against symbolic value with constructor '" ++ d ++ "'"
sUnify p sv = substError $
  "Unexpected type error occurred\n\
  \trying to unify concrete pattern '"
  ++ show p  ++ "' against symbolic value '"
  ++ show sv ++ "'"

sUnifyMany :: [(Pattern a, SValue)] -> Substitution
sUnifyMany =
  foldr (\(p, sv) u -> u <> sUnify p sv) mempty
