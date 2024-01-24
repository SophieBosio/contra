module PartialEvaluator where

import Syntax
import Interpreter (substitute, pair)

import Control.Monad.Reader
import Control.Monad.State


-- Abbreviations
type PEvalState a = ReaderT (Program a) (State (Program a))


-- Export
partiallyEvaluate :: Program a -> Program a
partiallyEvaluate = undefined


-- Main functions
partial :: Term a -> PEvalState a (Term a)
partial t | canonical t = return t
partial (Pattern (Variable x a)) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program) of
       [ ] -> return $ Pattern $ Variable x a
       -- [t] -> return $ ???
       _   -> error  $ "ambiguous bindings for " ++ show x
partial (Pattern (Pair t0 t1 a)) =
  do t0' <- partial t0
     t1' <- partial t1
     return $ Pattern $ Pair t0' t1' a
partial (Pattern (Constructor c ps a)) =
  do ts  <- mapM partial (Pattern <$> ps)
     ps' <- mapM (return . strengthenToPattern) ts
     return $ Pattern $ Constructor c ps' a
partial (Rec x t0 a) = undefined -- isn't this just the same as interpreter?
partial (Let x t0 t1 a) =
  do notAtTopLevel (x, a)
     t0' <- partial t0
     partial $ substitute x t1 t0'
partial (Lambda x t0 a) = undefined
partial (Application t1 t2 a) = undefined
partial (Case t0 ts a) = undefined
partial (Fst p a) = undefined
partial (Snd p a) = undefined
partial (Plus t1 t2 a) = undefined
partial (Minus t1 t2 a) = undefined
partial (Lt t1 t2 a) = undefined
partial (Gt t1 t2 a) = undefined
partial (Equal t1 t2 a) = undefined
partial (Not t0 a) = undefined
partial t = error $ "Partial evaluation failed for term " ++ show t


-- Utility
notAtTopLevel :: (X, a) -> PEvalState a ()
notAtTopLevel (x, _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "the name " ++ x ++ "shadows the top level declaration of " ++ x
