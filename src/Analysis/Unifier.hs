{-

  Module      : Analysis.Unifier
  Description : Unification algorithm for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  Unification algorithm for Contra.

  A PatternMatch is either unsuccessful or it is given by a Transformation
  from 'Pattern a' to 'Pattern a'.

  We find the Transformation by unifying two patterns.

  The result of unification is a Substitution with a Unifier. Either a Unifier
  doesn't exist for the two patterns, or is it a map from pattern to pattern,
  that maps all the free variables in each pattern to a concrete pattern such
  that the two unify.

  If this Unifier exists, that constitutes our Transformation.

-}

module Analysis.Unifier where

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


-- Substitution is, conveniently, a semigroup and a monoid!
instance Semigroup (Substitution meta a) where
  s <> s' = Substitution $ unifier s <> unifier s'

instance Monoid (Substitution meta a) where
  mempty  = Substitution $ return []
  mappend = (<>)


-- Helpers
mapsTo :: Pattern a -> Pattern a -> Transformation Pattern a
mapsTo p q = return (p, q)

replaces :: Pattern a -> Pattern a -> Substitution Pattern a
replaces p q = Substitution $ return $ q `mapsTo` p


-- Exports
patternMatch :: Show a => Pattern a -> Term a -> PatternMatch a
patternMatch p q = maybe NoMatch MatchBy (unifier $ unify p q)

applyTransformation :: Show a => Transformation Pattern a -> Term a -> Term a
applyTransformation xs t =
  foldr ((\(x, s) t' -> substitute x t' s) . second weakenToTerm) t xs

firstMatch :: Show a => (Monad m) => Pattern a -> [(Pattern a, Term a)]
           -> m (Transformation Pattern a, Term a)
firstMatch v [] = error $ "No match for " ++ show v ++ " in case statement"
firstMatch v ((p, t) : rest) =
  case patternMatch v (Pattern p) of
       NoMatch   -> firstMatch v rest
       MatchBy u -> return (u, t)

substitute :: Show a => Pattern a -> Term a -> (Term a -> Term a)
-- 'substitute p t s' computes t[s/p]
-- I.e., substitute all occurrences of pattern p in term t with term s
-- TODO: The three 'substitute' cases for Constructors should be pretty easy to refactor
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
  | otherwise = v `replaces` w
unifyPattern v@(Variable x _) p                | not $ p `contains` x = p `replaces` v
-- unifyPattern (Variable {}) _ = Substitution Nothing
unifyPattern p                v@(Variable x _) | not $ p `contains` x = p `replaces` v
unifyPattern (List      ps _) (List     ps' _) =
  case validateUnifiers (zipWith unifyPattern ps ps') of
    Just us -> us
    Nothing -> Substitution Nothing
unifyPattern (PConstructor c ps _) (PConstructor c' ps' _)
  | c == c' && length ps == length ps'
  = case validateUnifiers (zipWith unifyPattern ps ps') of
      Just us -> us
      Nothing -> Substitution Nothing
unifyPattern (Value (VConstructor c vs _)) (PConstructor c' ps _)
  | c == c' && length vs == length ps
  = let ps' = map weakenToPattern vs
    in  case validateUnifiers (zipWith unifyPattern ps ps') of
          Just us -> us
          Nothing -> Substitution Nothing
unifyPattern (PConstructor c ps _) (Value (VConstructor c' vs _))
  | c == c' && length vs == length ps
  = let ps' = map weakenToPattern vs
    in  case validateUnifiers (zipWith unifyPattern ps ps') of
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


-- Subsitution helpers
substituteName :: Show a => X -> Term a -> (Term a -> Term a)
substituteName x t v = -- computes t[v/x]
  case t of
    Pattern (Variable        y _) | x == y -> v
    Pattern (List           ps a) -> Pattern $ List
                                     (map (manipulateWith subs) ps)  a
    Pattern (PConstructor c ps a) ->
      Pattern (PConstructor c (map (manipulateWith subs) ps) a)
    TConstructor         c ts  a  -> TConstructor    c (map subs ts) a
    Lambda               p t0  a  | not (p `contains` x)
                                  -> Lambda p    (subs t0)           a
    Application          t1 t2 a  -> Application (subs t1) (subs t2) a
    Let                p t1 t2 a  ->
      Let p (subs t1) ((if p `contains` x then id else subs) t2)     a
    Case  t0 ts  a                -> Case  (subs t0)
                                           (map (second subs) ts)    a
    Plus  t0 t1  a                -> Plus  (subs t0) (subs t1)       a
    Minus t0 t1  a                -> Minus (subs t0) (subs t1)       a
    Lt    t0 t1  a                -> Lt    (subs t0) (subs t1)       a
    Gt    t0 t1  a                -> Gt    (subs t0) (subs t1)       a
    Equal t0 t1  a                -> Equal (subs t0) (subs t1)       a
    Not   t0     a                -> Not   (subs t0)                 a
    _                             -> t
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
freeVariables (Lambda       x t _) =
  let bound = freeVariables' x
  in  [ y | y <- freeVariables t, y `notElem` bound ]
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
