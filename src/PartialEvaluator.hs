module PartialEvaluator where

import Syntax
import Unification
  ( substitute,
    applyTransformation
  )
import Interpreter
  ( boolean, number,
    firstMatch
  )

import Control.Monad.Reader
import Control.Monad.State
import Data.Hashable


-- Abbreviations
type Environment  a = Program a
type PartialState a = StateT (Environment a) (Reader (Environment a))


-- Export
partiallyEvaluate :: Show a => Program a -> (Term a -> (Term a, Program a))
partiallyEvaluate p t =
  let (specialised, residual) = runReader (runStateT (partial [] t) p) p
  in  (specialised, residual)


-- Memoisation
addSpecialised :: F -> Term a -> (Environment a -> Environment a)
addSpecialised f t p =
  case lookup f (functions p ++ properties p) of
    Just  _ -> p
    Nothing -> Function f t End <> p

bind :: F -> Term a -> PartialState a ()
bind f t = do
  newEnv <- lift $ local (addSpecialised f t) ask
  put newEnv


-- Main functions
partial :: Show a => [Name] -> Term a -> PartialState a (Term a)
partial ns (Pattern p) = partialPattern ns p
partial ns (TConstructor c ts a) =
  do ts' <- mapM (partial ns) ts
     return $ strengthenIfPossible c ts' a
partial ns (Let (Variable x b) t0 t1 a) =
  do notAtTopLevel (x, a)
     t0' <- partial ns t0
     if canonical t0'
       then partial ns $ substitute x t1 t0'
       else do t1' <- partial ns t1
               return $ Let (Variable x b) t0' t1' a
partial ns (Lambda (Variable x b) t0 a) =
  do let (ns', x', alphaT0) = alpha ns x t0
     t0' <- partial ns' alphaT0
     return $ Lambda (Variable x' b) t0' a
-- Specialise named function
partial ns (Application t1@(Pattern (Variable x _)) t2 a) =
  do t2' <- partial ns t2
     env <- ask
     let x' = x ++ show t2'
     case lookup x' (functions env) of
       Just  s -> return s -- Already specialised
       Nothing -> if canonical t2'
                     then do t1' <- partial ns t1
                             f <- function t1'
                             specialised <- partial ns (f t2')
                             bind x' specialised
                             return specialised
                     else do t1' <- partial ns t1
                             return $ Application t1' t2' a
-- Specialise anonymous function
partial ns (Application t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t2'
       then do f <- function t1'
               partial ns (f t2')
       else return $ Application t1' t2' a
partial ns (Case t0 ts a) =
  do v <- partial ns t0
     if canonical v
       then do (u, t) <- firstMatch v ts
               partial ns $ applyTransformation u t
       else do alts   <- mapM (partial ns . weakenToTerm . fst) ts
               let alts' = map strengthenToPattern alts
               bodies <- mapM (partial ns . snd) ts
               return $ Case v (zip alts' bodies) a
partial ns (Plus t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t2'
               return $ Pattern $ Value $ Number (m + n) a
       else return $ Plus t1' t2' a
partial ns (Minus t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t2'
               return $ Pattern $ Value $ Number (m - n) a
       else return $ Minus t1' t2' a
partial ns (Lt t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Boolean (m < n) a
       else return $ Lt t1' t2' a
partial ns (Gt t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Boolean (m > n) a
       else return $ Gt t1' t2' a
partial ns (Equal t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t1'
               return $ Pattern $ Value $ Boolean (m == n) a
       else return $ Equal t1' t2' a
partial ns (Not t0 a) =
  do t0' <- partial ns t0
     if canonical t0'
       then do b <- boolean t0'
               return $ Pattern $ Value $ Boolean (not b) a
       else return $ Not t0' a
-- partial (Rec x t0 a) =
--   do notAtTopLevel (x, a)
--      partial $ substitute x t0 (Rec x t0 a)

partialPattern :: Show a => [Name] -> Pattern a -> PartialState a (Term a)
partialPattern _ (Value v) = partialValue v
partialPattern ns (Variable x a) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program ++ properties program) of
       [ ] -> return $ Pattern $ Variable x a
       [t] -> partial ns t
       _   -> error  $ "ambiguous bindings for " ++ show x
partialPattern ns (PConstructor c ps a) =
  do ts  <- mapM (partialPattern ns) ps
     return $ strengthenIfPossible c ts a

partialValue :: Show a => Value a -> PartialState a (Term a)
partialValue v = return $ Pattern $ Value v


-- Utility
function :: Show a => Term a -> PartialState a (Term a -> Term a)
function (Lambda (Variable x _) t a) =
  do notAtTopLevel (x, a)
     return $ substitute x t
function t = error $ "expected a function, but got " ++ show t

notAtTopLevel :: (X, a) -> PartialState a ()
notAtTopLevel (x, _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "the name " ++ x ++ "shadows the top level declaration of " ++ x

-- Alpha renaming
alpha :: Show a => [Name] -> Name -> Term a -> ([Name], Name, Term a)
alpha ns x t
  | x `elem` ns = let x' = show $ hash (show x ++ show t)
                  in  if x' `elem` ns
                         then alpha ns x' t
                         else (ns ++ [ x'], x', subst x x' t)
  | otherwise   = (ns, x, t)

subst :: Show a => X -> X -> Term a -> Term a
subst x x' (Pattern (Variable y a)) | x == y = Pattern (Variable x' a)
subst x x' (Pattern (PConstructor c ps a)) =
  let ps' = map (manipulateWith (subst x x')) ps
  in  Pattern (PConstructor c ps' a)
subst x x' (Lambda (Variable y b) t0 a)
  | x == y = Lambda (Variable x' b) (subst x x' t0) a
subst x x' (Application t1 t2 a) = Application (subst x x' t1) (subst x x' t2) a
subst _ _  t@(Let            {}) = t -- local scope takes precedence
subst _ _  t@(Case           {}) = t -- local scope takes precedence
subst x x' (Plus        t0 t1 a) = Plus  (subst x x' t0) (subst x x' t1) a
subst x x' (Minus       t0 t1 a) = Minus (subst x x' t0) (subst x x' t1) a
subst x x' (Lt          t0 t1 a) = Lt    (subst x x' t0) (subst x x' t1) a
subst x x' (Gt          t0 t1 a) = Gt    (subst x x' t0) (subst x x' t1) a
subst x x' (Equal       t0 t1 a) = Equal (subst x x' t0) (subst x x' t1) a
subst x x' (Not         t0    a) = Not   (subst x x' t0) a
subst x x' (TConstructor c ts a) =
  let ts' = map (subst x x') ts
  in  TConstructor c ts' a
subst _ _ t = t
