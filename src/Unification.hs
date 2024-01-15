module Unification where

import Syntax


-- Abbreviations
-- Meta is a placeholder for the Pattern/Term constructors
type Transformation meta a = (meta a -> meta a)

data PatternMatch a =
    NoMatch
  | MatchBy (Transformation Pattern a)

errorMessage :: Term a -> Pattern a -> b
errorMessage p q = error $
  "couldn't match " ++ show p ++ " against pattern " ++ show q

type Unifier a = Maybe (a -> a)

newtype Substitution meta a = Substitution { unifier :: Unifier (meta a) }


-- Export
patternMatch :: Term a -> Pattern a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)


-- Unification
unify :: Term a -> Pattern a -> Substitution Pattern a
unify (Pattern p1) = unify' p1
-- unify Rec         X      (T0 a)            a
-- unify Let         X      (T1 a) (T2 a)     a
-- unify Application (T1 a) (T2 a)            a
-- unify Case        (T0 a) [(Alt a, Body a)] a
--   -- Utilities:
-- unify Fst         (T0 a)                   a
-- unify Snd         (T0 a)                   a
-- unify Plus        (T0 a) (T1 a)            a
-- unify Minus       (T0 a) (T1 a)            a 
-- unify Lt          (T0 a) (T1 a)            a
-- unify Gt          (T0 a) (T1 a)            a
-- unify Equal       (T0 a) (T1 a)            a
-- unify Not         (T0 a)                   a

unify' :: Pattern a -> Pattern a -> Substitution Pattern a
unify' (Variable x _) (Variable y _) | x == y = mempty
unify' (Variable x _) p              | not $ p `contains` x = p `substitutes` x
unify' p              (Variable x _) | not $ p `contains` x = p `substitutes` x
-- unify' (Constructor c ps _) (Constructor c' ps' _)
--   | c == c' && length ps == length ps'
--   = 
-- unify' (Unit _)
-- unify' (Number n _)
-- unify' (Boolean b _)
-- unify' (Pair t0 t1)


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
