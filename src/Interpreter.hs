module Interpreter where

import Syntax
import Unification

import Control.Monad.Reader
import Control.Arrow (second)


-- Abbreviation
type Runtime a = Reader (Program a)

-- Export
normalise :: Show a => Program a -> (Term a -> Value a)
normalise p t =
  case runReader (evaluate t) p of
    (Pattern (Value v)) -> v
    _                   -> error $ "failed to normalise term " ++ show t


-- Main functions
evaluate :: Show a => Term a -> Runtime a (Term a)
evaluate (Pattern p) = evaluatePattern p
evaluate (Let x t0 t1 a) =
  do notAtTopLevel (x, a)
     evaluate t0 >>= evaluate . substitute x t1
evaluate (Application t1 t2 _) =
  do f <- evaluate t1 >>= function
     x <- evaluate t2
     evaluate (f x)
evaluate (Case t0 ts _) =
  do v      <- evaluate t0
     (u, t) <- firstMatch v ts
     evaluate $ applyTransformation u t
evaluate (Plus t1 t2 a) =
  do m <- evaluate t1 >>= number
     n <- evaluate t2 >>= number
     return $ Pattern $ Value $ Number (m + n) a
evaluate (Minus t1 t2 a) =
  do m <- evaluate t1 >>= number
     n <- evaluate t2 >>= number
     return $ Pattern $ Value $ Number (m - n) a
evaluate (Lt    t0 t1 a) =
  do m <- evaluate t0 >>= number
     n <- evaluate t1 >>= number
     return $ Pattern $ Value $ Boolean (m < n) a
evaluate (Gt    t0 t1 a) =
  do m <- evaluate t0 >>= number
     n <- evaluate t1 >>= number
     return $ Pattern $ Value $ Boolean (m > n) a
evaluate (Equal t0 t1 a) =
  do m <- evaluate t0 >>= number
     n <- evaluate t1 >>= number
     return $ Pattern $ Value $ Boolean (m == n) a
evaluate (Not t0 a) =
  do b <- evaluate t0 >>= boolean
     return $ Pattern $ Value $ Boolean (not b) a
evaluate _ = error "expected a non-canonical term!"
-- evaluate (Rec x t0 a) =
--   do notAtTopLevel (x, a)
--      evaluate $ substitute x t0 (Rec x t0 a)

evaluatePattern :: Show a => Pattern a -> Runtime a (Term a)
evaluatePattern (Value v) = evaluateValue v
evaluatePattern (Variable x _) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program) of
       [ ] -> error $ "unbound variable" ++ x
       [t] -> evaluate t -- Disallow shadowing at top-level
       _   -> error $ "ambiguous bindings for " ++ x
evaluatePattern (PConstructor c ps a) =
  do ts  <- mapM evaluatePattern ps
     let ps = map strengthenToPattern ts
     return $ Pattern $ PConstructor c ps a

evaluateValue :: Show a => Value a -> Runtime a (Term a)
evaluateValue v = return $ Pattern $ Value v


-- Substitution & Pattern matching
substitute :: X -> Term a -> (Term a -> Term a)
substitute x t v = -- computes t[v/x]
  case t of
    Pattern (Variable  y  _) | x == y -> v
    Pattern (PConstructor c ps a) ->
      Pattern (PConstructor c (map (manipulateWith subs) ps) a)
    TConstructor c ts a     -> TConstructor    c (map subs ts) a
    Lambda  y t1 a | x /= y -> Lambda y (subs t1)              a
    Application  t1 t2 a    -> Application (subs t1) (subs t2) a
    Let  y t1 t2 a          ->
      Let y (subs t1) ((if x == y then id else subs) t2) a
    Plus  t0 t1  a          -> Plus  (subs t0) (subs t1)       a
    Minus t0 t1  a          -> Minus (subs t0) (subs t1)       a
    Lt    t0 t1  a          -> Lt    (subs t0) (subs t1)       a
    Gt    t0 t1  a          -> Gt    (subs t0) (subs t1)       a
    Equal t0 t1  a          -> Equal (subs t0) (subs t1)       a
    Not   t0     a          -> Not   (subs t0)                 a
    _                         -> t
    -- Rec  y t1    a | x /= y -> Rec y (subs t1)                 a
  where
    subs = flip (substitute x) v

firstMatch :: (Monad m) => Term a -> [(Pattern a, Term a)]
           -> m (Transformation Pattern a, Term a)
firstMatch v [] = error $ "No match for " ++ show v ++ " in case statement"
firstMatch v ((p, t) : rest) =
  case patternMatch v (weakenToTerm p) of
       NoMatch   -> firstMatch v rest
       MatchBy u -> return (u, t)

applyTransformation :: Transformation Pattern a -> Term a -> Term a
applyTransformation xs t =
  foldr ((\(x, v) t' -> substitute x t' v) . second weakenToTerm) t xs


-- Utility functions
number :: (Show a, Monad m) => Term a -> m Integer
number (Pattern (Value (Number n _))) = return n
number t = error $ "expected an integer, but got a " ++ show t

boolean :: (Show a, Monad m) => Term a -> m Bool
boolean (Pattern (Value (Boolean b _))) = return b
boolean t = error $ "expected a boolean value, but got a " ++ show t

function :: Show a => Term a -> Runtime a (Term a -> Term a)
function (Lambda x t a) =
  do notAtTopLevel (x, a)
     return $ substitute x t
function t = error $ "expected a function, but got a " ++ show t

notAtTopLevel :: (X, a) -> Runtime a ()
notAtTopLevel (x, _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "the name " ++ x ++ "shadows the top level declaration of " ++ x
