{-------------------------------------------------------------------------------

  Module      : Semantics.PartialEvaluator
  Description : Partial evaluator for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  Partial evaluator for Contra, based on online partial evaluation.

  The PartialState monad keeps track of the following contexts:
   - State  : Program Type, which is keeps track of specialised functions
   - Reader : Program Type, which is the original, typed program text

-------------------------------------------------------------------------------}

module Semantics.PartialEvaluator where

import Core.Syntax
import Analysis.Unifier
import Semantics.Interpreter (boolean, number)

import Control.Monad.Reader
import Control.Monad.State
import Data.Hashable


-- Abbreviations
type Environment  = Program Type
type PartialState = StateT Environment (Reader Environment)


-- Export
partiallyEvaluate :: Program Type -> (Term Type -> (Term Type, Program Type))
partiallyEvaluate p t =
  let (specialised, residual) = runReader (runStateT (partial [] t) p) p
  in  (specialised, residual)


-- Memoisation
addSpecialised :: F -> Term Type -> (Environment -> Environment)
addSpecialised f t p =
  case lookup f (functions p ++ properties p) of
    Just  _ -> p
    Nothing -> Function f t End <> p

bind :: F -> Term Type -> PartialState ()
bind f t = do
  newEnv <- lift $ local (addSpecialised f t) ask
  put newEnv


-- Main functions
partial :: [Name] -> Term Type -> PartialState (Term Type)
partial ns (Pattern p) = partialPattern ns p
partial ns (TConstructor c ts a) =
  do ts' <- mapM (partial ns) ts
     return $ strengthenIfPossible c ts' a
partial ns (Lambda p t a) =
  do let fvs = freeVariables' p
     let (ns', alphaP, alphaT) = alpha fvs ns p t
     t'  <- partial ns' alphaT
     return $ Lambda alphaP t' a
partial ns (Let p t1 t2 a) =
  do notAtTopLevel p
     t'  <- partialPattern ns p
     t1' <- partial ns t1
     let p' = strengthenToPattern t'
     if canonical t1'
       then case patternMatch p' t1' of
         MatchBy u -> partial ns (applyTransformation u t2)
         NoMatch   -> error $ "Couldn't unify '" ++ show p ++
                              "' against '" ++ show t1 ++ "'."
       else return $ Let p' t1' t2 a
-- Specialise named function (denoted by a variable name)
partial ns (Application t1@(Pattern (Variable x _)) t2 a) =
  do t2' <- partial ns t2
     env <- get
     let x' = x ++ show t2'
     case lookup x' (functions env) of
       Just  s -> return s -- Already specialised
       Nothing -> if canonical t2'
                     then do t1' <- partial ns t1
                             f   <- function t1'
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
       then do (u, t) <- firstMatch (strengthenToPattern v) ts
               partial ns $ applyTransformation u t
       else do alts   <- mapM (partial ns . weakenToTerm . fst) ts
               bodies <- mapM (partial ns . snd) ts
               let alts' = map strengthenToPattern alts
               let cases = zip alts' bodies
               let ts'   = eliminateUnreachable (strengthenToPattern v) cases
               return $ Case v ts' a
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
-- partial (Rec x t0 a) = -- future work

partialPattern :: [Name] -> Pattern Type -> PartialState (Term Type)
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

partialValue :: Value Type -> PartialState (Term Type)
partialValue v = return $ Pattern $ Value v


-- Alpha renaming
alpha :: Show a => [Name] -> [Name] -> Pattern a -> Term a
      -> ([Name], Pattern a, Term a)
alpha [     ] ns p t = (ns, p, t)
alpha (x:fvs) ns p t =
  let (ns', p', t') = alpha' ns x
  in  alpha fvs ns' p' t'
  where
    alpha' ms y
      | y `elem` ms = let y' = show $ hash (show x ++ show t)
                        in  if y' `elem` ms
                               then alpha' ms y'
                               else (ms ++ [y'], replaceWithIn' y y' p, replaceWithIn y y' t)
      | otherwise = (ms, p, t)

-- replace x with x' in t
replaceWithIn :: Show a => X -> X -> Term a -> Term a
replaceWithIn x x' (Pattern     p) = Pattern $ replaceWithIn' x x' p
replaceWithIn x x' (Lambda p t a) =
  Lambda (manipulateWith (replaceWithIn x x') p) (replaceWithIn x x' t)  a
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

replaceWithIn' :: Show a => X -> X -> Pattern a -> Pattern a
replaceWithIn' x x' (Variable y a) | x == y = Variable x' a
replaceWithIn' x x' (PConstructor c ps a) =
  let ps' = map (manipulateWith (replaceWithIn x x')) ps
  in  PConstructor c ps' a
replaceWithIn' x x' (List ps a) =
  let ps' = map (manipulateWith (replaceWithIn x x')) ps
  in  List ps' a
replaceWithIn' _ _ p = p


-- Eliminating unreachable paths in case statement
eliminateUnreachable :: Show a => Pattern a -> [(Pattern a, Term a)] -> [(Pattern a, Term a)]
eliminateUnreachable p =
  foldr (\(alt, body) ts' -> case patternMatch p (Pattern alt) of
          NoMatch   -> ts'
          MatchBy _ -> ts' ++ [(alt, body)]
        ) []


-- Utility
function :: Show a => Term a -> PartialState (Term a -> Term a)
function (Lambda p t _) =
  do notAtTopLevel p
     return $ substitute p t
function t = error $ "Expected a function, but got the term '" ++ show t ++ "'"

notAtTopLevel :: Pattern a -> PartialState ()
notAtTopLevel (Variable x _) =
  do program <- ask
     when (x `elem` (fst <$> functions program)) $
       error $ "The name '" ++ x ++
               "' shadows the top level declaration of '" ++ x ++ "'."
notAtTopLevel (PConstructor _ ps _) = mapM_ notAtTopLevel ps
notAtTopLevel (List           ps _) = mapM_ notAtTopLevel ps
notAtTopLevel _                     = return ()
