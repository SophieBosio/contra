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
type Environment  a = Program a
type PartialState a = StateT (Environment a) (Reader (Environment a))


-- Export
partiallyEvaluate :: Show a => Program a -> (Term a -> (Term a, Program a))
partiallyEvaluate p t =
  let (specialised, residual) = runReader (runStateT (partial t) p) p
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
partial :: Show a => Term a -> PartialState a (Term a)
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
-- Specialise named function
partial (Application t1@(Pattern (Variable x _)) t2 a) =
  do t2' <- partial t2
     env <- ask
     let x' = x ++ show t2'
     case lookup x' (functions env) of
       Just  s -> return s -- Already specialised
       Nothing -> if canonical t2'
                     then do t1' <- partial t1
                             f <- function t1'
                             specialised <- partial (f t2')
                             bind x' specialised
                             return specialised
                     else do t1' <- partial t1
                             return $ Application t1' t2' a
-- Specialise anonymous function
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

partialPattern :: Show a => Pattern a -> PartialState a (Term a)
partialPattern (Value v) = partialValue v
partialPattern (Variable x a) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program ++ properties program) of
       [ ] -> return $ Pattern $ Variable x a
       [t] -> partial t
       _   -> error  $ "ambiguous bindings for " ++ show x
partialPattern (PConstructor c ps a) =
  do ts  <- mapM partialPattern ps
     return $ strengthenIfPossible c ts a

partialValue :: Show a => Value a -> PartialState a (Term a)
partialValue v = return $ Pattern $ Value v



-- memoise :: Show a => Term a -> Term a -> a -> PartialState a (Term a)
-- memoise def arg a =
--   do let x' = show $ hash $ show arg
--      program <- get
--      case lookup x' (functions program) of
--        Just def' -> return $ Application def' arg a
--        Nothing   -> do f <- function def
--                        def' <- partial (f arg)
--                        put (program <> Function x' def' End)
--                        return $ Application def' arg a

-- Utility
alpha :: Name -> Term a -> Term a
alpha = undefined

function :: Show a => Term a -> PartialState a (Term a -> Term a)
function (Lambda x t a) =
  do notAtTopLevel (x, a)
     return $ substitute x t
function t = error $ "expected a function, but got " ++ show t

notAtTopLevel :: (X, a) -> PartialState a ()
notAtTopLevel (x, _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "the name " ++ x ++ "shadows the top level declaration of " ++ x

specialisedProgram :: Program a -> [(F, Term a)] -> Program a
specialisedProgram = undefined -- TODO:
