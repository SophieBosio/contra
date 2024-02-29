module Unification where

import Syntax

import Control.Arrow (second)


-- Abbreviations
-- Meta is a placeholder for the Pattern/Term constructors
type Transformation meta a = [(X, meta a)]

data PatternMatch a =
    NoMatch
  | MatchBy (Transformation Pattern a)

type Unifier a = Maybe [(X, a)]

newtype Substitution meta a = Substitution { unifier :: Unifier (meta a) }
  
-- Exports
patternMatch :: Show a => Term a -> Term a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)

applyTransformation :: Show a => Transformation Pattern a -> Term a -> Term a
applyTransformation xs t =
  foldr ((\(x, v) t' -> substitute x t' v) . second weakenToTerm) t xs

substitute :: Show a => X -> Term a -> (Term a -> Term a)
substitute x t v = -- computes t[v/x]
  case t of
    Pattern (Variable  y  _) | x == y -> v
    Pattern (PConstructor c ps a) ->
      Pattern (PConstructor c (map (manipulateWith subs) ps) a)
    TConstructor c ts a           -> TConstructor    c (map subs ts) a
    Lambda v'@(Variable y _) t1 a  | x /= y
                                  -> Lambda v' (subs t1)              a
    Application  t1 t2 a          -> Application (subs t1) (subs t2) a
    Let v'@(Variable y _) t1 t2 a ->
      Let v' (subs t1) ((if x == y then id else subs) t2) a
    Plus  t0 t1  a                -> Plus  (subs t0) (subs t1)       a
    Minus t0 t1  a                -> Minus (subs t0) (subs t1)       a
    Lt    t0 t1  a                -> Lt    (subs t0) (subs t1)       a
    Gt    t0 t1  a                -> Gt    (subs t0) (subs t1)       a
    Equal t0 t1  a                -> Equal (subs t0) (subs t1)       a
    Not   t0     a                -> Not   (subs t0)                 a
    _                             -> t
    -- Rec  y t1    a | x /= y -> Rec y (subs t1)                 a
  where
    subs = flip (substitute x) v


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


-- Free Variables
freeVariables :: Term a -> [Name]
freeVariables (Pattern           p) = freeVariables' p
freeVariables (TConstructor _ ts _) = concatMap freeVariables ts
freeVariables (Lambda       x t0 _) = freeVariables' x ++ freeVariables t0
freeVariables (Application t1 t2 _) = freeVariables t1 ++ freeVariables t2
freeVariables (Let       x t1 t2 _) = freeVariables' x ++ freeVariables t1
                                                       ++ freeVariables t2
freeVariables (Case        t0 bs _) = freeVariables t0 ++
                                      concatMap (freeVariables' . fst) bs ++
                                      concatMap (freeVariables  . snd) bs
freeVariables (Plus        t0 t1 _) = freeVariables t0 ++ freeVariables t1
freeVariables (Minus       t0 t1 _) = freeVariables t0 ++ freeVariables t1
freeVariables (Lt          t0 t1 _) = freeVariables t0 ++ freeVariables t1
freeVariables (Gt          t0 t1 _) = freeVariables t0 ++ freeVariables t1
freeVariables (Equal       t0 t1 _) = freeVariables t0 ++ freeVariables t1
freeVariables (Not            t0 _) = freeVariables t0

freeVariables' :: Pattern a -> [Name]
freeVariables' (Value             _) = mempty
freeVariables' (Variable     x    _) = return x
freeVariables' (PConstructor x ps _) =
  [ y | y <- foldr (\p acc -> acc <> freeVariables' p) mempty ps, x /= y ]


-- Utility functions
contains :: Pattern a -> X -> Bool
contains (Variable        x _) y | x == y = True
contains (PConstructor _ ps _) y = any (`contains` y) ps
contains _                     _ = False

mapsTo :: X -> Pattern a -> Transformation Pattern a
mapsTo x p = return (x, p)
