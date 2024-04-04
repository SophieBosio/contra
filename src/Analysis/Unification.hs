module Analysis.Unification where

import Core.Syntax

import Control.Arrow (second)
import Data.Maybe    (isNothing)


-- Abbreviations
-- Meta is a placeholder for the Pattern/Term constructors
type Transformation meta a = [(meta a, meta a)]

data PatternMatch a =
    NoMatch
  | MatchBy (Transformation Pattern a)
  deriving (Show)

type Unifier a = Maybe [(a, a)]

newtype Substitution meta a = Substitution { unifier :: Unifier (meta a) }
  deriving Show

mapsTo :: Pattern a -> Pattern a -> Transformation Pattern a
mapsTo x p = return (x, p)


-- Exports
patternMatch :: Show a => Pattern a -> Term a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)

applyTransformation :: Show a => Transformation Pattern a -> Term a -> Term a
applyTransformation xs t =
  foldr ((\(x, v) t' -> substitute x t' v) . second weakenToTerm) t xs

firstMatch :: Show a => (Monad m) => Pattern a -> [(Pattern a, Term a)]
           -> m (Transformation Pattern a, Term a)
firstMatch v [] = error $ "No match for " ++ show v ++ " in case statement"
firstMatch v ((p, t) : rest) =
  case patternMatch v (weakenToTerm p) of
       NoMatch   -> firstMatch v rest
       MatchBy u -> return (u, t)


-- 'substitute p t s' computes t[s/p]
-- I.e., the term t with the term s instead of the pattern p
substitute :: Show a => Pattern a -> Term a -> (Term a -> Term a)
substitute (Variable     x    _) t s = substituteName x t s
substitute (PConstructor p cs _) t (Pattern (Value (VConstructor q ds _)))
  | p == q    = foldr (\(x, s) t' -> substitute x t' s) t
                (zip cs (map (weakenToTerm . weakenToPattern) ds))
  | otherwise = t
substitute (PConstructor p cs _) t (Pattern (PConstructor q ds _))
  | p == q    = foldr (\(x, s) t' -> substitute x t' s) t
                (zip cs (map weakenToTerm ds))
  | otherwise = t
substitute (PConstructor p cs _) t (TConstructor q ds _)
  | p == q    = foldr (\(x, s) t' -> substitute x t' s) t (zip cs ds)
  | otherwise = t
substitute (List ps _) t (Pattern (List qs _))
  | length ps == length qs = foldr (\(p, q) t' -> substitute p t' (Pattern q)) t
                             (zip ps qs)
  | otherwise = t
substitute _ t _ = t


-- Unification
unify :: Show a => Pattern a -> Term a -> Substitution Pattern a
unify p (Pattern q) = unifyPattern p q
unify p (TConstructor c ts a)
  | all canonical ts
  = unifyPattern p (PConstructor c  (map strengthenToPattern ts)  a)
unify _ _ = Substitution Nothing -- Only patterns can match patterns

unifyPattern :: Pattern a -> Pattern a -> Substitution Pattern a
unifyPattern (Value        v) (Value        w) = unifyValue v w
unifyPattern v@(Variable x _) w@(Variable y _)
  | x == y    = mempty
  | otherwise = v `substitutes` w
unifyPattern v@(Variable x _) p                | not $ p `contains` x = p `substitutes` v
unifyPattern p                v@(Variable x _) | not $ p `contains` x = p `substitutes` v
unifyPattern (List      ps _) (List     ps' _) =
  case validateUnifiers (zipWith unifyPattern ps ps') of
    Just us -> us
    Nothing -> Substitution Nothing
unifyPattern (PConstructor c ps _) (PConstructor c' ps' _)
  | c == c' && length ps == length ps'
  = case validateUnifiers (zipWith unifyPattern ps ps') of
      Just us -> us
      Nothing -> Substitution Nothing
unifyPattern _             _                 = Substitution Nothing

unifyValue :: Value a -> Value a -> Substitution Pattern a
unifyValue (Unit       _) (Unit         _) = mempty
unifyValue (Number   n _) (Number     m _) | n == m = mempty
unifyValue (Boolean  b _) (Boolean    c _) | b == c = mempty
unifyValue (VConstructor c vs _) (VConstructor c' vs' _)
  | c == c' && length vs == length vs'
  = case validateUnifiers (zipWith unifyValue vs vs') of
      Just us -> us
      Nothing -> Substitution Nothing
unifyValue _             _                 = Substitution Nothing


-- Substitution
instance Semigroup (Substitution meta a) where
  s <> s' = Substitution $ unifier s <> unifier s'

instance Monoid (Substitution meta a) where
  mempty  = Substitution $ return []
  mappend = (<>)

substitutes :: Pattern a -> Pattern a -> Substitution Pattern a
substitutes p x = Substitution $ return $ x `mapsTo` p

substituteName :: Show a => X -> Term a -> (Term a -> Term a)
substituteName x t v = -- computes t[v/x]
  case t of
    Pattern (Variable        y _) | x == y -> v
    Pattern (List           ps a) -> Pattern $ List
                                     (map (manipulateWith subs) ps)  a
    Pattern (PConstructor c ps a) ->
      Pattern (PConstructor c (map (manipulateWith subs) ps) a)
    TConstructor c ts a           -> TConstructor    c (map subs ts) a
    Lambda v'@(Variable y _) t1 a | x /= y
                                  -> Lambda v' (subs t1)             a
    Application  t1 t2 a          -> Application (subs t1) (subs t2) a
    Let v'@(Variable y _) t1 t2 a ->
      Let v' (subs t1) ((if x == y then id else subs) t2) a
    Case  t0 ts  a                -> Case  (subs t0)
                                           (map (second subs) ts)    a
    Plus  t0 t1  a                -> Plus  (subs t0) (subs t1)       a
    Minus t0 t1  a                -> Minus (subs t0) (subs t1)       a
    Lt    t0 t1  a                -> Lt    (subs t0) (subs t1)       a
    Gt    t0 t1  a                -> Gt    (subs t0) (subs t1)       a
    Equal t0 t1  a                -> Equal (subs t0) (subs t1)       a
    Not   t0     a                -> Not   (subs t0)                 a
    _                             -> t
    -- Rec  y t1    a | x /= y  -> Rec y (subs t1)                 a
  where
    subs = flip (substituteName x) v

validateUnifiers :: [Substitution meta a] -> Maybe (Substitution meta a)
validateUnifiers us
  | any (isNothing . unifier) us = Nothing
  | otherwise                    = Just $ foldr (flip (<>)) mempty us


-- Free Variables
freeVariables :: Term a -> [Name]
freeVariables (Pattern           p) = freeVariables' p
freeVariables (TConstructor _ ts _) = concatMap freeVariables ts
freeVariables (Lambda       x t0 _) =
  let bound = freeVariables' x
  in  [ y | y <- freeVariables t0, y `notElem` bound ]
freeVariables (Application t1 t2 _) = freeVariables t1 ++ freeVariables t2
freeVariables (Let       x t1 t2 _) =
  let bound = freeVariables' x
  in     freeVariables t1
      <> [ y | y <- freeVariables t2, y `notElem` bound ]
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
freeVariables' (List           ps _) =
  foldr (\p acc -> acc <> freeVariables' p) mempty ps
freeVariables' (PConstructor x ps _) =
  [ y | y <- foldr (\p acc -> acc <> freeVariables' p) mempty ps, x /= y ]


-- Utility functions
contains :: Pattern a -> X -> Bool
contains (Variable         x _) y | x == y = True
contains (List            ps _) y = any (`contains` y) ps
contains (PConstructor _  ps _) y = any (`contains` y) ps
contains _                     _ = False
