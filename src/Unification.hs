module Unification where

import Syntax


-- Abbreviations
-- Meta is a placeholder for the Pattern/Term constructors
type Transformation meta a = [(X, meta a)]

data PatternMatch a =
    NoMatch
  | MatchBy (Transformation Pattern a)

type Unifier a = Maybe [(X, a)]

newtype Substitution meta a = Substitution { unifier :: Unifier (meta a) }
  
-- Export
patternMatch :: Show a => Term a -> Term a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)


-- Unification
unify :: Show a => Term a -> Term a -> Substitution Pattern a
unify (Pattern p) (Pattern q) = unify' p q
unify (TConstructor c ts a) (TConstructor c' ts' a')
  | all canonical ts && all canonical ts'
  = unify' (PConstructor c  (map strengthenToPattern ts)  a)
           (PConstructor c' (map strengthenToPattern ts') a')
unify _ _ = Substitution Nothing -- Only patterns can match patterns

unify' :: Pattern a -> Pattern a -> Substitution Pattern a
unify' (Value      v) (Value      w) = unify'' v w
unify' (Variable x _) (Variable y _) | x == y = mempty
unify' (Variable x _) p              | not $ p `contains` x = p `substitutes` x
unify' p              (Variable x _) | not $ p `contains` x = p `substitutes` x
unify' (PConstructor c ps _) (PConstructor c' ps' _)
  | c == c' && length ps == length ps'
  = foldr (mappend . uncurry unify') mempty (zip ps ps')
unify' _             _                 = Substitution Nothing

unify'' :: Value a -> Value a -> Substitution Pattern a
unify'' (Unit       _) (Unit         _) = mempty
unify'' (Number   n _) (Number     m _) | n == m = mempty
unify'' (Boolean  b _) (Boolean    c _) | b == c = mempty
unify'' (VConstructor c vs _) (VConstructor c' vs' _)
  | c == c' && length vs == length vs'
  = foldr (mappend . uncurry unify'') mempty (zip vs vs')
unify'' _             _                 = Substitution Nothing


-- Substitution
instance Semigroup (Substitution meta a) where
  s <> s' = Substitution $ unifier s <> unifier s'

instance Monoid (Substitution meta a) where
  mempty = Substitution $ return []
  mappend = (<>)

substitutes :: Pattern a -> X -> Substitution Pattern a
substitutes p x = Substitution $ return $ x `mapsTo` p


-- Utility functions
contains :: Pattern a -> X -> Bool
contains (Variable        x _) y | x == y = True
contains (PConstructor _ ps _) y = any (`contains` y) ps
contains _                     _ = False

mapsTo :: X -> Pattern a -> Transformation Pattern a
mapsTo x p = return (x, p)
