{-# LANGUAGE TypeOperators #-}

module TypeInferrer where

import Syntax

import Control.Monad.RWS

-- Abbreviations
data Constraint = Type :=: Type
  deriving Show

type Mapping  a b = a -> b
type MapsTo   a b = Mapping a b -> Mapping a b
type Environment  = Mapping Name Type
type Annotation   = RWS Environment [Constraint] Index
type Substitution = [(Index, Type)]


-- Setup
fresh :: Annotation Type
fresh = Variable' <$> (get >>= \i ->     -- Get current index (state)
                          put (i + 1) >> -- Increment
                          return i)      -- Return fresh

bind :: Eq x => x -> a -> x `MapsTo` a
bind x a look y = if x == y
                     then a
                     else look y

hasSameTypeAs :: Term Type -> Term Type -> Annotation ()
t0 `hasSameTypeAs` t1 = tell [annotation t0 :=: annotation t1]

hasType :: Term Type -> Type -> Annotation ()
t0 `hasType` tau = tell [annotation t0 :=: tau]

class HasSubstitution a where
  substitute :: Type -> Index -> (a -> a)

instance HasSubstitution Type where
  substitute = undefined

instance HasSubstitution Constraint where
  substitute = undefined

emptyEnvironment :: Environment
emptyEnvironment = error . (++ " is unbound!")


-- Main functions
annotate :: Term a -> Annotation (Term Type)
annotate (Pattern     p) = annotate' p
annotate (Lambda x t0 _) =
  do tau <- fresh
     t0' <- local (bind x tau) $ annotate t0
     return $ Lambda x t0' (tau :->: annotation t0')
-- annotate (Rec x t0 _) =
--   do tau <- fresh
--      t0' <- local (bind x tau) $ annotate t0
--      return $ Rec x t0' $ annotation t0'
annotate (Let x t1 t2 _) =
  do t1' <- annotate t1
     t2' <- local (bind x (annotation t1')) $ annotate t2
     return $ Let x t1' t2' (annotation t2')
annotate (Application t1 t2 _) =
  do tau <- fresh
     t1' <- annotate t1
     t2' <- annotate t2
     t1' `hasType` (annotation t2' :->: tau)
     return $ Application t1' t2' tau
annotate (Case t0 ts _) =
  do tau1 <- fresh
     tau2 <- fresh
     t0'  <- annotate t0
     t0' `hasType` tau1
     fvs  <- mapM (\x -> (,) x <$> fresh) $ concatMap (freeVariables . fst) ts
     ps'  <- local (liftFreeVariables fvs) $ mapM (annotate . weakenToTerm . fst) ts
     ps'' <- mapM (return . strengthenToPattern) ps'
     bs'  <- local (liftFreeVariables fvs) $ mapM (annotate . snd) ts
     mapM_ (`hasType` tau1) ps'
     mapM_ (`hasType` tau2) bs'
     return $ Case t0' (zip ps'' bs') tau2
annotate (Plus t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     t0' `hasType` Integer'
     t1' `hasType` Integer'
     return $ Plus t0' t1' Integer'
annotate (Minus t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     t0' `hasType` Integer'
     t1' `hasType` Integer'
     return $ Minus t0' t1' Integer'
annotate (Lt t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     t0' `hasType` Integer'
     t1' `hasType` Integer'
     return $ Lt t0' t1' Boolean'
annotate (Gt t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     t0' `hasType` Integer'
     t1' `hasType` Integer'
     return $ Gt t0' t1' Boolean'
annotate (Equal t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     t0' `hasSameTypeAs` t1'
     return $ Equal t0' t1' Boolean'
annotate (Not t0 _) =
  do t0' <- annotate t0
     t0' `hasType` Boolean'
     return $ Not t0' Boolean'

annotate' :: Pattern a -> Annotation (Term Type)
annotate' (Variable  x _) =
  do env <- ask
     return $ Pattern $ Variable x $ env x
annotate' (Constructor c ts _) =
  do tau <- fresh
     ts' <- local (bind c tau) $ mapM annotate' ts
     ps' <- mapM (return . strengthenToPattern) ts'
     return $ Pattern $ Constructor c ps' tau
annotate' (Unit        _) = return $ Pattern $ Unit Unit'
annotate' (Number    n _) = return $ Pattern $ Number n Integer'
annotate' (Boolean   b _) = return $ Pattern $ Boolean b Boolean'

solve :: [Constraint] -> Maybe Substitution
solve [                 ] = return mempty
solve (constraint : rest) =
  case constraint of
    Unit'         :=: Unit'         -> solve rest
    Integer'      :=: Integer'      -> solve rest
    Boolean'      :=: Boolean'      -> solve rest
    (t0 :*:  t1)  :=: (t2 :*:  t3)  -> solve $ (t0 :=: t2) : (t1 :=: t3) : rest
    (t0 :->: t1)  :=: (t2 :->: t3)  -> solve $ (t0 :=: t2) : (t1 :=: t3) : rest
    (ADT  x1 t1)  :=: (ADT  x2 t2)  ->
      if   x1 /= x2
      then Nothing
      else solve $ zipWith (:=:) t1 t2 ++ rest
    (Variable' i) :=: t1            ->
      if   i `elem` indices t1
      then (if Variable' i /= t1 then Nothing else solve rest)
      else do c <- solve (substitute t1 i <$> rest)
              return $ (i, t1) : c
    t0 :=: Variable' i ->
      if   i `elem` indices t0
      then (if Variable' i /= t0 then Nothing else solve rest)
      else do c <- solve (substitute t0 i <$> rest)
              return $ (i, t0) : c
    _                               -> error $ show constraint


-- Utility functions
indices :: Type -> [Index]
indices (Variable' i) = return i
indices (ADT    _ ts) = concatMap indices ts
indices (t0  :*:  t1) = indices t0 ++ indices t1
indices (t0  :->: t1) = indices t0 ++ indices t1
indices _             = mempty

freeVariables :: Pattern a -> [Name]
freeVariables (Unit         _) = mempty
freeVariables (Number     _ _) = mempty
freeVariables (Boolean    _ _) = mempty
freeVariables (Variable   x _) = return x
freeVariables (Constructor x ps _) =
  [ y | y <- foldr (\p acc -> acc <> freeVariables p) mempty ps, x /= y ]
freeVariables _ = mempty

liftFreeVariables :: [(Name, Type)] -> (Environment -> Environment)
liftFreeVariables [              ] e = e
liftFreeVariables ((x, t) : rest) e = bind x t $ liftFreeVariables rest e

refine :: Substitution -> (Type -> Type)
refine s o = refine' s o
  where
    refine' [          ] t             = t
    refine' _            Unit'         = Unit'
    refine' _            Integer'      = Integer'
    refine' _            Boolean'      = Boolean'
    refine' ((i, t) : _) (Variable' j)
      | i == j = refine' s t
    refine' (_   : rest) (Variable' j) = refine' rest (Variable' j)
    refine' s'           (t0  :*:  t1) = refine' s' t0 :*:  refine' s' t1
    refine' s'           (t0  :->: t1) = refine' s' t0 :->: refine' s' t1
    refine' s'           (ADT    x ts) =
      ADT x $ map (refine' s') ts

