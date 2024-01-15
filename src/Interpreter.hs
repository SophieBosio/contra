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
-- evaluate (Fst p _) =
--   do ts <- evaluate p >>= pair
--      return $ fst ts
-- evaluate (Snd p _) =
--   do ts <- evaluate p >>= pair
--      return $ snd ts
-- evaluate (Plus t1 t2 a) =
--   do m <- evaluate t1 >>= number
--      n <- evaluate t2 >>= number
--      return $ Number (m + n) a
-- evaluate (Minus t1 t2 a) =
--   do m <- evaluate t1 >>= number
--      n <- evaluate t2 >>= number
--      return $ Number (m - n) a
-- evaluate (Lt    t0 t1 a) =
--   do m <- evaluate t0 >>= number
--      n <- evaluate t1 >>= number
--      return $ Boolean (m < n) a
-- evaluate (Gt    t0 t1 a) =
--   do m <- evaluate t0 >>= number
--      n <- evaluate t1 >>= number
--      return $ Boolean (m > n) a
-- evaluate (Equal t0 t1 a) =
--   do m <- evaluate t0 >>= number
--      n <- evaluate t1 >>= number
--      return $ Boolean (m == n) a
-- evaluate (Not t0 a) =
--   do b <- evaluate t0 >>= bool
--      return $ Boolean (not b) a
-- evaluate _ = error "expected a non-canonical term!"




-- Utility functions
substitute :: X -> Term a -> (Term a -> Term a)
substitute = undefined

-- strengthenToPattern :: Term a -> Runtime a (Pattern a)
-- strengthenToPattern (Pattern p) = return p
-- strengthenToPattern _           = error "expected pattern, but got general term"

