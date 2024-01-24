module PartialEvaluator where

import Syntax
import Interpreter
  ( evaluate, substitute,
    bool, number, pair,
    firstMatch, applyTransformation
  )

import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow ((***))


-- Abbreviations
type PEvalState a = ReaderT (Program a) (State (Program a))


-- Export
partiallyEvaluate :: Show a => Program a -> Program a
partiallyEvaluate = undefined


-- Main functions
partial :: Show a => Term a -> PEvalState a (Term a)
partial t | canonical t = return t
partial (Pattern (Variable x a)) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program) of
       [ ] -> return $ Pattern $ Variable x a
       -- [t] -> return $ ??? -- FIXME
       _   -> error  $ "ambiguous bindings for " ++ show x
partial (Pattern (Pair t0 t1 a)) =
  do t0' <- partial t0
     t1' <- partial t1
     return $ Pattern $ Pair t0' t1' a
partial (Pattern (Constructor c ps a)) =
  do ts  <- mapM partial (Pattern <$> ps)
     ps' <- mapM (return . strengthenToPattern) ts
     return $ Pattern $ Constructor c ps' a
partial (Rec x t0 a) =
  do notAtTopLevel (x, a)
     partial $ substitute x t0 (Rec x t0 a)
partial (Let x t0 t1 a) =
  do notAtTopLevel (x, a)
     t0' <- partial t0
     if canonical t0'
       then partial $ substitute x t1 t0'
       else do t1' <- partial t1
               return $ Let x t0' t1' a
partial (Lambda x t0 a) =
  do t0' <- partial t0
     return $ Lambda x t0' a
partial (Application t1 t2 a) = undefined
partial (Case t0 ts a) =
  do v <- partial t0
     if canonical v
       then do (u, t) <- firstMatch v ts
               partial $ applyTransformation u t
       else do alts   <- mapM (partial . weakenToTerm . fst) ts
               let alts' = map strengthenToPattern alts
               bodies <- mapM (partial . snd) ts
               return $ Case v (zip alts' bodies) a
partial (Fst p _) =
  do p' <- partial p >>= pair
     return $ fst p'
partial (Snd p _) =
  do p' <- partial p >>= pair
     return $ snd p'
partial (Plus t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Number (m + n) a
       else return $ Plus t1' t2' a
partial (Minus t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Number (m - n) a
       else return $ Minus t1' t2' a
partial (Lt t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Boolean (m < n) a
       else return $ Lt t1' t2' a
partial (Gt t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Boolean (m > n) a
       else return $ Gt t1' t2' a
partial (Equal t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Boolean (m == n) a
       else return $ Equal t1' t2' a
partial (Not t0 a) =
  do t0' <- partial t0
     if canonical t0'
       then do b <- bool t0'
               return $ Pattern $ Boolean (not b) a
       else return $ Not t0' a
partial t = error $ "Partial evaluation failed for term " ++ show t


-- Utility
function :: Show a => Term a -> PEvalState a (Term a -> Term a)
function (Lambda x t a) =
  do notAtTopLevel (x, a)
     return $ substitute x t
function t = error $ "expected a function, but got a " ++ show t

notAtTopLevel :: (X, a) -> PEvalState a ()
notAtTopLevel (x, _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "the name " ++ x ++ "shadows the top level declaration of " ++ x
