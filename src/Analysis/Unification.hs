module Analysis.Unification where

import Core.Syntax

import Control.Arrow (second)


-- Abbreviations
-- Meta is a placeholder for the Pattern/Term constructors
type Transformation meta a = [(meta a, meta a)]

data PatternMatch a =
    NoMatch
  | MatchBy (Transformation Pattern a)

type Unifier a = Maybe [(a, a)]

newtype Substitution meta a = Substitution { unifier :: Unifier (meta a) }
  
-- Exports
patternMatch :: Show a => Term a -> Term a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)

applyTransformation :: Show a => Transformation Pattern a -> Term a -> Term a
applyTransformation xs t =
  foldr ((\(x, v) t' -> substitute x t' v) . second weakenToTerm) t xs

-- 'substitute p t v' computes t[v/p]
-- I.e., the term t with the term v instead of the pattern p
substitute :: Show a => Pattern a -> Term a -> (Term a -> Term a)
substitute (Variable     x    _) t v = substituteName x t v
substitute (PConstructor p cs _) t (TConstructor q ds _)
  | p == q    = foldr (\(x, v) t' -> substitute x t' v) t (zip cs ds)
  | otherwise = t
substitute _ t _ = t


-- Unification
unify :: Show a => Term a -> Term a -> Substitution Pattern a
unify (Pattern p) (Pattern q) = unifyPattern p q
unify (TConstructor c ts a) (TConstructor c' ts' a')
  | all canonical ts && all canonical ts'
  = unifyPattern (PConstructor c  (map strengthenToPattern ts)  a)
           (PConstructor c' (map strengthenToPattern ts') a')
unify _ _ = Substitution Nothing -- Only patterns can match patterns

unifyPattern :: Pattern a -> Pattern a -> Substitution Pattern a
unifyPattern (Value        v) (Value        w) = unifyValue v w
unifyPattern (Variable   x _) (Variable   y _) | x == y = mempty
unifyPattern v@(Variable x _) p                | not $ p `contains` x = p `substitutes` v
unifyPattern p                v@(Variable x _) | not $ p `contains` x = p `substitutes` v
unifyPattern (Pair p1 p2 _) (Pair p1' p2' _) =
  unifyPattern p1 p1' <> unifyPattern p2 p2'
unifyPattern (PConstructor c ps _) (PConstructor c' ps' _)
  | c == c' && length ps == length ps'
  = foldr (mappend . uncurry unifyPattern) mempty (zip ps ps')
unifyPattern _             _                 = Substitution Nothing

unifyValue :: Value a -> Value a -> Substitution Pattern a
unifyValue (Unit       _) (Unit         _) = mempty
unifyValue (Number   n _) (Number     m _) | n == m = mempty
unifyValue (Boolean  b _) (Boolean    c _) | b == c = mempty
unifyValue (VConstructor c vs _) (VConstructor c' vs' _)
  | c == c' && length vs == length vs'
  = foldr (mappend . uncurry unifyValue) mempty (zip vs vs')
unifyValue _             _                 = Substitution Nothing


-- Substitution
instance Semigroup (Substitution meta a) where
  s <> s' = Substitution $ unifier s <> unifier s'

instance Monoid (Substitution meta a) where
  mempty = Substitution $ return []
  mappend = (<>)

substitutes :: Pattern a -> Pattern a -> Substitution Pattern a
substitutes p x = Substitution $ return $ x `mapsTo` p

substituteName :: Show a => X -> Term a -> (Term a -> Term a)
substituteName x t v = -- computes t[v/x]
  case t of
    Pattern (Variable        y  _) | x == y -> v
    Pattern (Pair         p1 p2 a) -> Pattern $ Pair
                                      (manipulateWith subs p1)
                                      (manipulateWith subs p2) a
    Pattern (PConstructor  c ps a) ->
      Pattern (PConstructor c (map (manipulateWith subs) ps) a)
    TConstructor c ts a            -> TConstructor    c (map subs ts) a
    Lambda v'@(Variable y _) t1 a  | x /= y
                                   -> Lambda v' (subs t1)             a
    Application  t1 t2 a           -> Application (subs t1) (subs t2) a
    Let v'@(Variable y _) t1 t2 a  ->
      Let v' (subs t1) ((if x == y then id else subs) t2) a
    Case  t0 ts  a                 -> Case  (subs t0)
                                            (map (second subs) ts)    a
    Plus  t0 t1  a                 -> Plus  (subs t0) (subs t1)       a
    Minus t0 t1  a                 -> Minus (subs t0) (subs t1)       a
    Lt    t0 t1  a                 -> Lt    (subs t0) (subs t1)       a
    Gt    t0 t1  a                 -> Gt    (subs t0) (subs t1)       a
    Equal t0 t1  a                 -> Equal (subs t0) (subs t1)       a
    Not   t0     a                -> Not   (subs t0)                 a
    _                              -> t
    -- Rec  y t1    a | x /= y  -> Rec y (subs t1)                 a
  where
    subs = flip (substituteName x) v


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
freeVariables' (Value              _) = mempty
freeVariables' (Variable     x     _) = return x
freeVariables' (Pair         p1 p2 _) = freeVariables' p1 <> freeVariables' p2
freeVariables' (PConstructor x  ps _) =
  [ y | y <- foldr (\p acc -> acc <> freeVariables' p) mempty ps, x /= y ]


-- Utility functions
contains :: Pattern a -> X -> Bool
contains (Variable         x _) y | x == y = True
contains (Pair         p1 p2 _) y = p1 `contains` y || p2 `contains` y
contains (PConstructor _  ps _) y = any (`contains` y) ps
contains _                     _ = False

mapsTo :: Pattern a -> Pattern a -> Transformation Pattern a
mapsTo x p = return (x, p)
