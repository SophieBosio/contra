module Interpreter where

import Syntax

import Control.Monad.Reader


-- Abbreviation
type Runtime a = Reader (Program a)

-- Export
normalise :: Show a => Program a -> (Term a -> Term a)
normalise p t = runReader (evaluate t) p


-- Main function
evaluate :: Show a => Term a -> Runtime a (Term a)
evaluate t | canonical t = return t
evaluate (Pattern (Variable x _)) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program) of
       [ ] -> error $ "unbound variable" ++ x
       [t] -> evaluate t -- Disallow shadowing at top-level
       _   -> error $ "ambiguous bindings for " ++ x
evaluate (Pattern (Pair t0 t1 a)) =
  do v0 <- evaluate t0
     v1 <- evaluate t1
     return $ (Pattern (Pair v0 v1 a))
evaluate (Pattern (Constructor c ps a)) =
  do ts  <- mapM evaluate (Pattern <$> ps) 
     ps' <- mapM (return . strengthenToPattern) ts
     return $ Pattern (Constructor c ps' a)
-- evaluate (Rec x t0 a) =
--   do notAtTopLevel (x, a)
--      evaluate (substitute x t0 (Rec x t0 a))
-- evaluate (Let x t0 t1 a) =
--   do notAtTopLevel (x, a)
--      evaluate t0 >>= evaluate . substitute x t1
-- evaluate (Application t1 t2 _) =
--   do f <- evaluate t1 >>= function
--      x <- evaluate t2
--      evaluate (f x)
-- evaluate (Case t0 ts _) =
--   do v  <- evaluate t0
--      let us = map (first $ unify v) ts
--      if null us
--         then error $ "no case matched " ++ show t0
--         else do let u = fst $ head us -- take the first possible unifier
--                 let t = snd $ head us -- take the corresponding branch
--                 evaluate $ substituteWithUnifier u t
evaluate (Fst p _) =
  do ts <- evaluate p >>= pair
     return $ fst ts
evaluate (Snd p _) =
  do ts <- evaluate p >>= pair
     return $ snd ts
evaluate (Plus t1 t2 a) =
  do m <- evaluate t1 >>= number
     n <- evaluate t2 >>= number
     return $ Pattern $ Number (m + n) a
evaluate (Minus t1 t2 a) =
  do m <- evaluate t1 >>= number
     n <- evaluate t2 >>= number
     return $ Pattern $ Number (m - n) a
evaluate (Lt    t0 t1 a) =
  do m <- evaluate t0 >>= number
     n <- evaluate t1 >>= number
     return $ Pattern $ Boolean (m < n) a
evaluate (Gt    t0 t1 a) =
  do m <- evaluate t0 >>= number
     n <- evaluate t1 >>= number
     return $ Pattern $ Boolean (m > n) a
evaluate (Equal t0 t1 a) =
  do m <- evaluate t0 >>= number
     n <- evaluate t1 >>= number
     return $ Pattern $ Boolean (m == n) a
evaluate (Not t0 a) =
  do b <- evaluate t0 >>= bool
     return $ Pattern $ Boolean (not b) a
evaluate _ = error "expected a non-canonical term!"


-- Substitution
substitute :: X -> Term a -> (Term a -> Term a)
substitute x t v = -- computes t[v/x]
  case t of
    Pattern (Variable  y  _) | x == y -> v
    Pattern (Constructor c ps a) ->
      Pattern (Constructor c (map (manipulateWith subs) ps) a)
    Pattern (Pair  t1 t2 a) ->
      Pattern (Pair  (subs t1) (subs t2) a)
    Lambda  y t1 a | x /= y -> Lambda y (subs t1)              a
    Application  t1 t2 a    -> Application (subs t1) (subs t2) a
    Let  y t1 t2 a          ->
      Let y (subs t1) ((if x == y then id else subs) t2) a
    Rec  y t1    a | x /= y -> Rec y (subs t1)                 a
    Fst   t0     a          -> Fst   (subs t0)                 a
    Snd   t0     a          -> Snd   (subs t0)                 a
    Plus  t0 t1  a          -> Plus  (subs t0) (subs t1)       a
    Minus t0 t1  a          -> Minus (subs t0) (subs t1)       a
    Lt    t0 t1  a          -> Lt    (subs t0) (subs t1)       a
    Gt    t0 t1  a          -> Gt    (subs t0) (subs t1)       a
    Equal t0 t1  a          -> Equal (subs t0) (subs t1)       a
    Not   t0     a          -> Not   (subs t0)                 a
    _                         -> t
  where
    subs = flip (substitute x) v
    manipulateWith f = strengthenToPattern . f . weakenToTerm


-- Utility functions
bool :: Show a => Term a -> Runtime a Bool
bool (Pattern (Boolean b _)) = return b
bool t = error $ "expected a boolean value, but got a " ++ show t

number :: Show a => Term a -> Runtime a Integer
number (Pattern (Number n _)) = return n
number t = error $ "expected an integer, but got a " ++ show t

pair :: Show a => Term a -> Runtime a (Term a, Term a)
pair (Pattern (Pair t1 t2 _)) = return (t1, t2)
pair t = error $ "expected a pair, but got a " ++ show t

-- function :: Show a => Term a -> Runtime a (Term a -> Term a)
-- function (Lambda x t a) =
--   do notAtTopLevel (x, a)
--      return $ substitute x t
-- function t = error $ "expected a function, but got a " ++ show t
