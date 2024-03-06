module Semantics.Interpreter where

import Core.Syntax
import Analysis.Unification

import Control.Monad.Reader


-- Abbreviation
type Runtime a = Reader (Program a)

-- Export
runMain :: Show a => Program a -> Term a
runMain p = runReader (evaluate (mainFunction p)) p

normalise :: Show a => Program a -> (Term a -> Value a)
normalise p t =
  let result = runReader (evaluate t) p
  in  (strengthenToValue . strengthenToPattern) result


-- Main functions
evaluate :: Show a => Term a -> Runtime a (Term a)
evaluate (Pattern p) = evaluatePattern p
evaluate (TConstructor c ts a) =
  do ts' <- mapM evaluate ts
     return $ strengthenIfPossible c ts' a
evaluate (Let v@(Variable _ _) t0 t1 _) =
  do notAtTopLevel v
     evaluate t0 >>= evaluate . substitute v t1
evaluate (Let p@(PConstructor _ ps _) t0 t1 _) =
  do mapM_ notAtTopLevel ps
     p'  <- evaluatePattern p
     t0' <- evaluate t0
     case patternMatch p' t0' of
       MatchBy u -> evaluate (applyTransformation u t1)
       NoMatch   -> unificationError p t0
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
evaluate t = error $ "Malformed term '" ++ show t ++ "'."
-- evaluate (Rec x t0 a) =
--   do notAtTopLevel (x, a)
--      evaluate $ substitute x t0 (Rec x t0 a)

evaluatePattern :: Show a => Pattern a -> Runtime a (Term a)
evaluatePattern (Value v) = evaluateValue v
evaluatePattern (Variable x _) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program ++ properties program) of
       [ ] -> error $ "Unbound variable" ++ x
       [t] -> evaluate t -- Disallow shadowing at top-level
       _   -> error $ "Ambiguous bindings for " ++ x
evaluatePattern (PConstructor c ps a) =
  do ts <- mapM evaluatePattern ps
     return $ strengthenIfPossible c ts a

evaluateValue :: Show a => Value a -> Runtime a (Term a)
evaluateValue v = return $ Pattern $ Value v


-- Substitution & Pattern matching
firstMatch :: Show a => (Monad m) => Term a -> [(Pattern a, Term a)]
           -> m (Transformation Pattern a, Term a)
firstMatch v [] = error $ "No match for " ++ show v ++ " in case statement"
firstMatch v ((p, t) : rest) =
  case patternMatch v (weakenToTerm p) of
       NoMatch   -> firstMatch v rest
       MatchBy u -> return (u, t)


-- Utility functions
mainFunction :: Show a => Program a -> Term a
mainFunction (Function "main" t _) = t
mainFunction (Function   _ _ rest) = mainFunction rest
mainFunction (Property   _ _ rest) = mainFunction rest
mainFunction (Signature  _ _ rest) = mainFunction rest
mainFunction (Data       _ _ rest) = mainFunction rest
mainFunction End = error "No main function found."

number :: (Show a, Monad m) => Term a -> m Integer
number (Pattern (Value (Number n _))) = return n
number t = error $ "Expected an integer, but got a " ++ show t

boolean :: (Show a, Monad m) => Term a -> m Bool
boolean (Pattern (Value (Boolean b _))) = return b
boolean t = error $ "Expected a boolean value, but got a " ++ show t

function :: Show a => Term a -> Runtime a (Term a -> Term a)
function (Lambda v@(Variable _ _) t _) =
  do notAtTopLevel v
     return $ substitute v t
function (Lambda p@(PConstructor {}) t _) =
  return $ substitute p t
function t = error $ "Expected a function, but got a " ++ show t

notAtTopLevel :: Pattern a -> Runtime a ()
notAtTopLevel (Variable x _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "The name '" ++ x ++
               "' shadows the top level declaration of '" ++ x ++ "'."
notAtTopLevel _ = return ()

unificationError :: Pattern a -> Term a -> b
unificationError p t =
  error $ "Couldn't unify '" ++ show p ++ "' against '" ++ show t ++ "'."
