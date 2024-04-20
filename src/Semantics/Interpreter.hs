{-------------------------------------------------------------------------------

  Module      : Semantics.Interpreter
  Description : Interpreter for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  Interpreter for the functional language Contra.

  Mostly, variables are bound directly, as in function application or
  let-statements. Then, we can simply substitute the variable name(s) in the
  relevant term with the terms they are bound to.

  However, we cannot do this directly for top-level bindings. That's why the
  interpreter uses the Reader monad to access the program text.
  With it, we can find the function/property definition bound by that name in
  the program text and substitute the variable name for the definition.

-------------------------------------------------------------------------------}

module Semantics.Interpreter where

import Core.Syntax
import Analysis.Unifier

import Control.Monad.Reader


-- Abbreviation
type Runtime a = Reader (Program a)

-- Export
runMain :: (Show a, Eq a) => Program a -> Term a
runMain p = runReader (evaluate (mainFunction p)) p

normalise :: (Show a, Eq a) => Program a -> (Term a -> Value a)
normalise p t =
  let result = runReader (evaluate t) p
  in  (strengthenToValue . strengthenToPattern) result


-- Main functions
evaluate :: (Show a, Eq a) => Term a -> Runtime a (Term a)
evaluate (Pattern p) = evaluatePattern p
evaluate (TConstructor c ts a) =
  do ts' <- mapM evaluate ts
     return $ strengthenIfPossible c ts' a
evaluate (Lambda p t a) =
  return $ Lambda p t a
evaluate (Let p t1 t2 _) =
  do notAtTopLevel p
     t1' <- evaluate t1
     case patternMatch p t1' of
       MatchBy u -> evaluate (applyTransformation u t2)
       NoMatch   -> error $ "Couldn't unify '" ++ show p ++
                            "' against '" ++ show t1 ++ "'."
evaluate (Application t1 t2 _) =
  do f <- evaluate t1 >>= function
     x <- evaluate t2
     evaluate (f x)
evaluate (Case t0 ts _) =
  do v       <- evaluate t0
     (u, t)  <- firstMatch (strengthenToPattern v) ts
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
  do x <- evaluate t0
     y <- evaluate t1
     return $ Pattern $ Value $ Boolean (x == y) a
evaluate (Not t0 a) =
  do b <- evaluate t0 >>= boolean
     return $ Pattern $ Value $ Boolean (not b) a
-- evaluate (Rec p t a) = -- future work

evaluatePattern :: (Show a, Eq a) => Pattern a -> Runtime a (Term a)
evaluatePattern (Value v) = evaluateValue v
evaluatePattern (Variable x _) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program ++ properties program) of
       [ ] -> error $ "Unbound variable " ++ x ++ "!"
       [t] -> evaluate t
       -- Disallow shadowing at top-level
       _   -> error $ "Ambiguous bindings for '" ++ x ++ "'"
evaluatePattern (List ps a) =
  do ts <- mapM evaluatePattern ps
     let ps' = map strengthenToPattern ts
     return $ Pattern $ List ps' a
evaluatePattern (PConstructor c ps a) =
  do ts <- mapM evaluatePattern ps
     return $ strengthenIfPossible c ts a

evaluateValue :: (Show a, Eq a) => Value a -> Runtime a (Term a)
evaluateValue v = return $ Pattern $ Value v


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
number t = error $ "Expected an integer, but got the term '" ++ show t ++ "'"

boolean :: (Show a, Monad m) => Term a -> m Bool
boolean (Pattern (Value (Boolean b _))) = return b
boolean t = error $ "Expected a boolean, but got the term '" ++ show t ++ "'"

function :: Show a => Term a -> Runtime a (Term a -> Term a)
function (Lambda p t _) =
  do notAtTopLevel p
     return $ substitute p t
function t = error $ "Expected a function, but got a " ++ show t

notAtTopLevel :: Pattern a -> Runtime a ()
notAtTopLevel (Variable x _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "The name '" ++ x ++
               "' shadows the top level declaration of '" ++ x ++ "'."
notAtTopLevel (PConstructor _ ps _) = mapM_ notAtTopLevel ps
notAtTopLevel (List           ps _) = mapM_ notAtTopLevel ps
notAtTopLevel _                     = return ()
