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
{-# LANGUAGE LambdaCase #-}

module Validation.SymUnifier where

import Core.Syntax
import Validation.Formula
import Environment.ERSymbolic

import Data.SBV
import Data.List     (intercalate)
import Data.Foldable (foldrM)


-- * Abbreviations
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
substError =  Substitution . Left . return

substitution :: Transformation -> Substitution
substitution = Substitution . Right


-- * Export
symUnify :: Pattern Type -> SValue -> Formula PatternMatch
symUnify p sv =
  do result <- sUnify p sv
     case unifier result of
       Right bs -> return $ MatchBy bs
       Left err -> return $ NoMatch $ intercalate "\n" err

unifiable :: Pattern Type -> SValue -> PatternMatch
unifiable p sv =
  case unifier $ compatibleBy p sv of
    Right bs -> MatchBy bs
    Left err -> NoMatch $ intercalate "\n" err


-- * Main functions
sUnify :: Pattern Type -> SValue -> Formula Substitution
sUnify (Value v) sv = sUnifyValue v sv
sUnify (Variable x _) sv = return $ substitution $ bind x sv
sUnify (List ps _) (SArgs svs) =
  do foldrM (\(p, sv) u -> do u' <- sUnify p sv
                              return $ u <> u'
            ) mempty $ zip ps svs
sUnify (PConstructor c ps (ADT adt)) (SCtr adt' c' svs)
  | adt == adt'
  && c  == c' = foldrM (\(p, sv) u -> do u' <- sUnify p sv
                                         return $ u <> u'
                       ) mempty $ zip ps svs
-- sUnify (PConstructor c ps (ADT adt)) (SADT ident adt' si svs) = undefined
sUnify p sv = return $ substError $
  "Unexpected type error occurred \
  \trying to unify concrete pattern\n'"
  ++ show p  ++ "'\nagainst symbolic value\n'"
  ++ show sv ++ "'\n"

sUnifyValue :: Value Type -> SValue -> Formula Substitution
sUnifyValue (Unit      _) SUnit         = return mempty
sUnifyValue (Number  n _) (SNumber  sn) =
  do lift $ constrain $ sn .== literal n
     return mempty
sUnifyValue (Boolean b _) (SBoolean sb) =
  do lift $ constrain $ sb .== literal b
     return mempty
sUnifyValue (VConstructor c vs (ADT adt)) (SCtr adt' c' svs)
  | adt == adt'
  && c  == c' = foldrM (\(v, sv) u -> do u' <- sUnifyValue v sv
                                         return $ u <> u'
                       ) mempty $ zip vs svs
  | otherwise = return $ substError $
    "Type or constructor mismatch between concrete constructor\n'" ++ c ++
    "' of type '" ++ adt ++ "'\n and symbolic constructor\n'" ++ c' ++
    "' of type '" ++ adt' ++ "'\n"
sUnifyValue v sv = return $ substError $
  "Unexpected type error occurred\
  \trying to unify concrete value\n'"
  ++ show v  ++ "'\nagainst symbolic value\n'"
  ++ show sv ++ "'\n"

compatibleBy :: Pattern Type -> SValue -> Substitution
compatibleBy (Value             _) _            = mempty
compatibleBy (Variable     x    _) sv           = substitution $ bind x sv
compatibleBy (List           ps _) (SArgs  svs) =
  foldr (\(p, sv) u -> u <> compatibleBy p sv) mempty $ zip ps svs
compatibleBy (PConstructor c ps (ADT t)) (SCtr adt d svs)
  |  t == adt
  && c == d   = foldr (\(p, sv) u -> u <> compatibleBy p sv) mempty $ zip ps svs
  | otherwise = substError $
    "Unexpected type occurred when trying to unify\n\
    \concrete pattern with constructor '" ++ c ++ "' and type '" ++ show t
    ++ "' against symbolic value of type '" ++ d ++ "'"
compatibleBy p sv = substError $
  "Unexpected type error occurred\n\
  \trying to unify concrete pattern '"
  ++ show p  ++ "' against symbolic value '"
  ++ show sv ++ "'"
