{-# LANGUAGE FlexibleContexts #-}

module Unification where

import Syntax


-- Abbreviations
-- Meta is a placeholder for the Pattern/Term constructors
type Transformation meta a = (meta a -> meta a)

data PatternMatch a =
    NoMatch
  | MatchBy (Transformation Pattern a)

type Unifier a = Maybe (a -> a)

newtype Substitution meta a = Substitution { unifier :: Unifier (meta a) }


-- Export
patternMatch :: Term a -> Term a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)


-- Unification
unify :: Term a -> Term a -> Substitution Pattern a
unify (Pattern p) (Pattern q) = unify' p q
unify _            _          = Substitution Nothing

unify' :: Pattern a -> Pattern a -> Substitution Pattern a
unify' (Variable x _) (Variable y _) | x == y = mempty
unify' (Variable x _) p              | not $ p `contains` x = p `substitutes` x
unify' p              (Variable x _) | not $ p `contains` x = p `substitutes` x
unify' (Unit       _) (Unit         _) = mempty
unify' (Number   n _) (Number     m _) | n == m = mempty
unify' (Boolean  b _) (Boolean    c _) | b == c = mempty
unify' (Pair t0 t1 _) (Pair t0' t1' _) = unify t0 t0' `mappend` unify t1 t1'
unify' (Constructor c ps _) (Constructor c' ps' _)
  | c == c' && length ps == length ps'
  = foldr (mappend . uncurry unify') mempty (zip ps ps')
unify' _             _                 = Substitution Nothing


-- Substitution
instance Semigroup (Substitution meta a) where
  s <> s' = Substitution $ (.) <$> unifier s <*> unifier s'

instance Monoid (Substitution meta a) where
  mempty = Substitution $ return id
  mappend = (<>)

substitutes :: Pattern a -> X -> Substitution Pattern a
substitutes = undefined


-- Utility functions
isMatch :: PatternMatch meta -> Bool
isMatch NoMatch = False
isMatch _       = True

contains :: Pattern a -> X -> Bool
contains = undefined

-- mapsTo :: X -> Pattern a -> Transformation Pattern a
-- mapsTo (Variable x _) y | x == y = 
