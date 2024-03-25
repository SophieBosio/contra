module Semantics.PartialEvaluator where

import Core.Syntax
import Analysis.Unification
import Semantics.Interpreter
  ( boolean, number,
    firstMatch,
    unificationError
  )

import Control.Monad.Reader
import Control.Monad.State
import Data.Hashable
import Data.Set             (toList, fromList)


-- Abbreviations
type Environment  a = Program a
type PartialState a = StateT (Environment a) (Reader (Environment a))


-- Export
partiallyEvaluate :: (Show a, Eq a) => Program a -> (Term a -> (Term a, Program a))
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
partial :: (Show a, Eq a) => [Name] -> Term a -> PartialState a (Term a)
partial ns (Pattern p) = partialPattern ns p
partial ns (TConstructor c ts a) =
  do ts' <- mapM (partial ns) ts
     return $ strengthenIfPossible c ts' a
partial ns (Let v@(Variable x b) t0 t1 a) =
  do notAtTopLevel v
     t0' <- partial ns t0
     if canonical t0'
       then partial ns $ substitute v t1 t0'
       else do t1' <- partial ns t1
               return $ Let (Variable x b) t0' t1' a
partial ns (Let p@(PConstructor _ ps _) t0 t1 _) =
  do mapM_ notAtTopLevel ps
     p'  <- partialPattern ns p
     t0' <- partial ns t0
     case patternMatch p' t0' of
       MatchBy u -> partial ns (applyTransformation u t1)
       NoMatch   -> unificationError p t0
partial ns (Lambda (Variable x b) t0 a) =
  do let (ns', x', alphaT0) = alpha ns x t0
     t0' <- partial ns' alphaT0
     return $ Lambda (Variable x' b) t0' a
partial ns (Lambda (PConstructor c ps b) t0 a) =
  do let fvs = concatMap freeVariables' ps
     let ts  = map weakenToTerm ps
     let (ns', ts', alphaT0) = alphaAll fvs ns ts t0
     let ps' = map strengthenToPattern ts'
     t0' <- partial ns' alphaT0
     return $ Lambda (PConstructor c ps' b) t0' a
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
               n <- number t2'
               return $ Pattern $ Value $ Boolean (m < n) a
       else return $ Lt t1' t2' a
partial ns (Gt t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then do m <- number t1'
               n <- number t2'
               return $ Pattern $ Value $ Boolean (m > n) a
       else return $ Gt t1' t2' a
partial ns (Equal t1 t2 a) =
  do t1' <- partial ns t1
     t2' <- partial ns t2
     if canonical t1' && canonical t2'
       then return $ Pattern $ Value $ Boolean (t1' == t2') a
       else return $ Equal t1' t2' a
partial ns (Not t0 a) =
  do t0' <- partial ns t0
     if canonical t0'
       then do b <- boolean t0'
               return $ Pattern $ Value $ Boolean (not b) a
       else return $ Not t0' a
partial _ t = error $ "Malformed term '" ++ show t ++ "'."
-- partial (Rec x t0 a) =
--   do notAtTopLevel (x, a)
--      partial $ substitute x t0 (Rec x t0 a)

partialPattern :: (Show a, Eq a) => [Name] -> Pattern a -> PartialState a (Term a)
partialPattern _ (Value v) = partialValue v
partialPattern ns (Variable x a) =
  do program <- ask
     case map snd $ filter ((== x) . fst) (functions program ++ properties program) of
       [ ] -> return $ Pattern $ Variable x a
       [t] -> partial ns t
       _   -> error  $ "ambiguous bindings for " ++ show x
partialPattern ns (List ps a) =
  do ts <- mapM (partialPattern ns) ps
     let ps' = map strengthenToPattern ts
     return $ Pattern $ List ps' a
partialPattern ns (PConstructor c ps a) =
  do ts  <- mapM (partialPattern ns) ps
     return $ strengthenIfPossible c ts a

partialValue :: (Show a, Eq a) => Value a -> PartialState a (Term a)
partialValue v = return $ Pattern $ Value v


-- Alpha renaming
alpha :: Show a => [Name] -> Name -> Term a -> ([Name], Name, Term a)
alpha ns x t
  | x `elem` ns = let x' = show $ hash (show x ++ show t)
                  in  if x' `elem` ns
                         then alpha ns x' t
                         else (ns ++ [ x'], x', replaceWithIn x x' t)
  | otherwise   = (ns, x, t)

alphaAll :: Show a => [Name] -> [Name] -> [Term a] -> Term a
         -> ([Name], [Term a], Term a)
alphaAll [] [    ]  ts t0 = ([], ts, t0)
alphaAll ns fvs ts t0 =
  let (ns',  ts') = foldr (\t (ns'', ts'') ->
                             let (ns_, t_) = checkVars ns fvs t
                             in (ns'' ++ ns_, ts'' ++ [t_])) (ns, []) ts in
  let (ns'', t0') = checkVars ns' fvs t0 in
  let noDupsNs = removeDups ns''
  in (noDupsNs, ts', t0')
  where
    checkVars :: Show a => [Name] -> [Name] -> Term a -> ([Name], Term a)
    checkVars ns_ fvs_ t = foldr (\v (ns', _) ->
                                  let (ns'', _, t'') = alpha ns' v t
                                  in (ns' ++ ns'', t'')) (ns_, t) fvs_
    removeDups = toList . fromList

replaceWithIn :: Show a => X -> X -> Term a -> Term a
replaceWithIn x x' (Pattern (Variable y a)) | x == y = Pattern (Variable x' a)
replaceWithIn x x' (Pattern (PConstructor c ps a)) =
  let ps' = map (manipulateWith (replaceWithIn x x')) ps
  in  Pattern $ PConstructor c ps' a
replaceWithIn x x' (Pattern (List ps a)) =
  let ps' = map (manipulateWith (replaceWithIn x x')) ps
  in  Pattern $ List ps' a
replaceWithIn x x' (Lambda p t0 a) =
  Lambda (manipulateWith (replaceWithIn x x') p) (replaceWithIn x x' t0) a
replaceWithIn x x' (Application t1 t2 a) =
  Application (replaceWithIn x x' t1) (replaceWithIn x x' t2) a
replaceWithIn _ _  t@(Let            {}) = t -- local scope takes precedence
replaceWithIn _ _  t@(Case           {}) = t -- local scope takes precedence
replaceWithIn x x' (Plus        t0 t1 a) = Plus  (replaceWithIn x x' t0)
                                                 (replaceWithIn x x' t1) a
replaceWithIn x x' (Minus       t0 t1 a) = Minus (replaceWithIn x x' t0)
                                                 (replaceWithIn x x' t1) a
replaceWithIn x x' (Lt          t0 t1 a) = Lt    (replaceWithIn x x' t0)
                                                 (replaceWithIn x x' t1) a
replaceWithIn x x' (Gt          t0 t1 a) = Gt    (replaceWithIn x x' t0)
                                                 (replaceWithIn x x' t1) a
replaceWithIn x x' (Equal       t0 t1 a) = Equal (replaceWithIn x x' t0)
                                                 (replaceWithIn x x' t1) a
replaceWithIn x x' (Not         t0    a) = Not   (replaceWithIn x x' t0) a
replaceWithIn x x' (TConstructor c ts a) =
  let ts' = map (replaceWithIn x x') ts
  in  TConstructor c ts' a
replaceWithIn _ _ t = t


-- Utility
function :: Show a => Term a -> PartialState a (Term a -> Term a)
function (Lambda v@(Variable _ _) t _) =
  do notAtTopLevel v
     return $ substitute v t
function (Lambda p@(PConstructor {}) t _) =
  return $ substitute p t
function t = error $ "expected a function, but got " ++ show t

notAtTopLevel :: Pattern a -> PartialState a ()
notAtTopLevel (Variable x _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "the name " ++ x ++ "shadows the top level declaration of " ++ x
notAtTopLevel _ = return ()
