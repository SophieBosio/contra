module PartialEvaluator where

import Syntax
import Interpreter
  ( substitute,
    boolean, number,
    firstMatch, applyTransformation
  )

import Control.Monad.Reader
import Control.Monad.State


-- Abbreviations
type PEvalState a = ReaderT (Program a) (State (Program a))


-- Export
partiallyEvaluate :: Show a => Program a -> (Term a -> (Term a, Program a))
partiallyEvaluate p t = runState (runReaderT (partial t) p) p


-- Main functions
partial :: Show a => Term a -> PEvalState a (Term a)
partial (Pattern p) = partialPattern p
partial (TConstructor c ts a) =
  do ts' <- mapM partial ts
     return $ strengthenIfPossible c ts' a
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
-- /!\ Needs verification
-- TODO Memoisation
partial (Application t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t2'
       then do f <- function t1'
               partial (f t2')
       else return $ Application t1' t2' a
partial (Case t0 ts a) =
  do v <- partial t0
     if canonical v
       then do (u, t) <- firstMatch v ts
               partial $ applyTransformation u t
       else do alts   <- mapM (partial . weakenToTerm . fst) ts
               let alts' = map strengthenToPattern alts
               bodies <- mapM (partial . snd) ts
               return $ Case v (zip alts' bodies) a
partial (Plus t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Number (m + n) a
       else return $ Plus t1' t2' a
partial (Minus t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Number (m - n) a
       else return $ Minus t1' t2' a
partial (Lt t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Boolean (m < n) a
       else return $ Lt t1' t2' a
partial (Gt t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Boolean (m > n) a
       else return $ Gt t1' t2' a
partial (Equal t1 t2 a) =
  do t1' <- partial t1
     t2' <- partial t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Boolean (m == n) a
       else return $ Equal t1' t2' a
partial (Not t0 a) =
  do t0' <- partial t0
     if canonical t0'
       then do b <- boolean t0'
               return $ Pattern $ Value $ Boolean (not b) a
       else return $ Not t0' a
-- partial (Rec x t0 a) =
--   do notAtTopLevel (x, a)
--      partial $ substitute x t0 (Rec x t0 a)

partialPattern :: Show a => Pattern a -> PEvalState a (Term a)
partialPattern (Value v) = partialValue v
partialPattern (Variable x a) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program) of
       [ ] -> return $ Pattern $ Variable x a
       [t] -> return t
       _   -> error  $ "ambiguous bindings for " ++ show x
partialPattern (PConstructor c ps a) =
  do ts  <- mapM partialPattern ps
     return $ strengthenIfPossible c ts a

partialValue :: Show a => Value a -> PEvalState a (Term a)
partialValue v = return $ Pattern $ Value v


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
