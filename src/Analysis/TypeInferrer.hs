{-# LANGUAGE TypeOperators #-}

module Analysis.TypeInferrer where

import Core.Syntax
import Analysis.Unification
  ( freeVariables
  , freeVariables'
  )
import Environment.Environment
import Environment.ERWS

import Control.Monad (zipWithM_)
import Control.Arrow (second)
import Data.Maybe    (fromMaybe)

-- Abbreviations
data Constraint = Type :=: Type
  deriving Show

type Bindings         = Mapping Name Type
type Annotation     a = ERWS a Bindings [Constraint] Index
type TypeSubstitution = [(Index, Type)]


-- Export
inferProgram :: Program a -> Program Type
inferProgram program = flip addSignatures [] $
                       refine (resolveConstraints constraints)
                       <$> annotatedProgram
  where
    definitions prog = functions prog ++ properties prog
    constraints = annotationConstraints ++ signatureDefinitionAccord
    (annotatedProgram, _, annotationConstraints) =
      runERWS (annotateProgram program) program emptyBindings 0
    signatureDefinitionAccord =
      [ t' :=: annotation t'' | (x, t')  <- signatures  annotatedProgram
                              , (y, t'') <- definitions annotatedProgram
                              , x == y ]

inferTerm :: Term a -> Term Type
inferTerm t =
  let (t', _, _) = runERWS (annotate t) End emptyBindings 0
  in  t'


-- Setup
fresh :: Annotation a Type
fresh = Variable' <$> (get >>= \i ->     -- Get current index (state)
                          put (i + 1) >> -- Increment
                          return i)      -- Return fresh

bind :: Eq x => x -> a -> x `MapsTo` a
bind x a look y = if x == y then a else look y

hasSameTypeAs :: Term Type -> Term Type -> Annotation a ()
t0 `hasSameTypeAs` t1 = tell [annotation t0 :=: annotation t1]

hasType :: Term Type -> Type -> Annotation a ()
t0 `hasType` tau = tell [annotation t0 :=: tau]

class HasSubstitution a where
  substitution :: Type -> Index -> (a -> a)

instance HasSubstitution Type where
  substitution t i (Variable' j) | i == j = t
  substitution t i (t0 :->:  t1) = substitution t i t0 :->: substitution t i t1
  substitution _ _ t             = t

instance HasSubstitution Constraint where
  substitution t i (t0 :=: t1) = substitution t i t0 :=: substitution t i t1

emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound!")


-- Annotate program
annotateProgram :: Program a -> Annotation a (Program Type)
annotateProgram (Signature x def rest) =
  do i <- get
     let (j, tau) = alpha i def
     put j
     rest' <- local (bind x tau) $ annotateProgram rest
     return $ Signature x tau rest'
annotateProgram (Data t defs rest) =
  do i <- get
     let (j, defs') = alphaADT i defs
     put j
     rest' <- local (bind t (ADT t)) $ annotateProgram rest
     return $ Data t defs' rest'
annotateProgram (Function f def rest) =
  do def'  <- annotate def
     rest' <- annotateProgram rest
     return $ Function f def' rest'
annotateProgram (Property p def rest) =
  do def'  <- annotate def
     rest' <- annotateProgram rest
     mustReturnBool p def'
     return $ Property p def' rest'
annotateProgram End = return End


-- Annotate terms
annotate :: Term a -> Annotation a (Term Type)
annotate (Pattern p) = annotatePattern p
annotate (TConstructor c ts _) =
  do env <- environment
     adt <- datatype env c
     ts' <- mapM annotate ts
     cs  <- constructorTypes env c
     zipWithM_ hasType ts' cs
     return $ strengthenIfPossible c ts' (ADT adt)
annotate (Lambda (Variable x _) t0 _) =
  do tau <- fresh
     t0' <- local (bind x tau) $ annotate t0
     return $ Lambda (Variable x tau) t0' (tau :->: annotation t0')
annotate (Lambda p@(PConstructor {}) t0 _) =
  do tau1 <- fresh
     tau2 <- fresh
     t'   <- annotatePattern p
     t' `hasType` tau1
     let p' = strengthenToPattern t'
     fvs  <- mapM (\x -> (,) x <$> fresh) $ freeVariables t0
     t0'  <- local (liftFreeVariables fvs) $ annotate t0
     t0' `hasType` tau2
     return $ Lambda p' t0' (tau1 :->: tau2)
annotate (Lambda (Value v) t0 _) =
  do t'  <- annotateValue v
     let v' = (strengthenToValue . strengthenToPattern) t'
     t0' <- annotate t0
     let tau1 = annotation v'
     let tau2 = annotation t0'
     return $ Lambda (Value v') t0' (tau1 :->: tau2)
annotate (Let (Variable x _) t1 t2 _) =
  do t1' <- annotate t1
     let tau = annotation t1'
     t2' <- local (bind x tau) $ annotate t2
     return $ Let (Variable x tau) t1' t2' (annotation t2')
annotate (Let p@(PConstructor {}) t1 t2 _) =
  do t'  <- annotatePattern p
     t1' <- annotate t1
     t' `hasSameTypeAs` t1'
     let p' = strengthenToPattern t'
     fvs <- mapM (\x -> (,) x <$> fresh) $ freeVariables t2
     t2' <- local (liftFreeVariables fvs) $ annotate t2
     return $ Let p' t1' t2' (annotation t2')
annotate (Let (Value v) t1 t2 _) =
  do t'  <- annotateValue v
     let v'  = (strengthenToValue . strengthenToPattern) t'
     let tau = annotation v'
     t1' <- annotate t1
     t1' `hasType` tau
     t2' <- annotate t2
     return $ Let (Value v') t1' t2' (annotation t2')
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
     fvs  <- mapM (\x -> (,) x <$> fresh) $ concatMap (freeVariables' . fst) ts
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
-- annotate (Rec x t0 _) =
--   do tau <- fresh
--      t0' <- local (bind x tau) $ annotate t0
--      return $ Rec x t0' $ annotation t0'

annotatePattern :: Pattern a -> Annotation a (Term Type)
annotatePattern (Value      v) = annotateValue v
annotatePattern (Variable x _) =
  do bindings <- ask
     return $ Pattern $ Variable x (bindings x)
annotatePattern (PConstructor c ps _) =
  do env <- environment
     adt <- datatype env c
     ts' <- mapM annotatePattern ps
     cs  <- constructorTypes env c
     zipWithM_ hasType ts' cs
     return $ strengthenIfPossible c ts' (ADT adt)

annotateValue :: Value a -> Annotation a (Term Type)
annotateValue (Unit        _) = return $ Pattern $ Value $ Unit Unit'
annotateValue (Number    n _) = return $ Pattern $ Value $ Number n Integer'
annotateValue (Boolean   b _) = return $ Pattern $ Value $ Boolean b Boolean'
annotateValue (VConstructor c vs _) =
  do env <- environment
     adt <- datatype env c
     ts' <- mapM annotateValue vs
     cs  <- constructorTypes env c
     zipWithM_ hasType ts' cs
     return $ strengthenIfPossible c ts' (ADT adt)


-- Resolve constraints
resolveConstraints :: [Constraint] -> TypeSubstitution
resolveConstraints = fromMaybe (error "Type error occurred") . solve

solve :: [Constraint] -> Maybe TypeSubstitution
solve [                 ] = return mempty
solve (constraint : rest) =
  case constraint of
    Unit'         :=: Unit'         -> solve rest
    Integer'      :=: Integer'      -> solve rest
    Boolean'      :=: Boolean'      -> solve rest
    (t0 :->: t1)  :=: (t2 :->: t3)  -> solve $ (t0 :=: t2) : (t1 :=: t3) : rest
    (ADT     x1)  :=: (ADT     x2)  ->
      if   x1 /= x2
      then Nothing
      else solve rest
    (Variable' i) :=: t1            ->
      if   i `elem` indices t1
      then (if Variable' i /= t1 then Nothing else solve rest)
      else do c <- solve (substitution t1 i <$> rest)
              return $ (i, t1) : c
    t0 :=: Variable' i ->
      if   i `elem` indices t0
      then (if Variable' i /= t0 then Nothing else solve rest)
      else do c <- solve (substitution t0 i <$> rest)
              return $ (i, t0) : c
    _                               -> error $ show constraint

refine :: TypeSubstitution -> (Type -> Type)
refine [            ] t                      = t
refine s@((i, u) : _) (Variable' j) | i == j = refine s u
refine (_     : rest) (Variable' j)          = refine rest (Variable' j)
refine _              Unit'                  = Unit'
refine _              Integer'               = Integer'
refine _              Boolean'               = Boolean'
refine s              (tau1 :->: tau2)       = refine s tau1 :->: refine s tau2
refine _              (ADT name)             = ADT name


-- Utility functions
indices :: Type -> [Index]
indices (Variable' i) = return i
indices (t0  :->: t1) = indices t0 ++ indices t1
indices _             = mempty

liftFreeVariables :: [(Name, Type)] -> (Bindings -> Bindings)
liftFreeVariables [             ] e = e
liftFreeVariables ((x, t) : rest) e = bind x t $ liftFreeVariables rest e

alpha :: Index -> (Type -> (Index, Type))
alpha i t =
  (if null (indices t)
     then i
     else i + maximum (indices t) + 1,
  increment t)
  where
    increment :: Type -> Type
    increment (Variable'    j) = Variable' (i + j)
    increment (tau1 :->: tau2) = increment tau1 :->: increment tau2
    increment t'               = t'

alphaADT :: Index -> [Constructor] -> (Index, [Constructor])
alphaADT i = foldr (\c (j, k) -> second (: k) (alphaDef j c)) (i, [])

alphaDef :: Index -> Constructor -> (Index, Constructor)
alphaDef i (Constructor c cs) = second (Constructor c)
                                  (foldr (\t (j, ts) ->
                                          second (: ts) (alpha j t)) (i, []) cs)

returnType :: Type -> Type
returnType (_ :->: t2) = returnType t2
returnType t           = t

mustReturnBool :: P -> Term Type -> Annotation a ()
mustReturnBool p t =
  case returnType (annotation t) of
    Boolean' -> return ()
    _        -> error $
      "Type error: Property '" ++ show p ++ "'must return Boolean."


addSignatures :: Program Type -> [Name] -> Program Type
addSignatures p@(Function f t rest) sigs =
  case lookup f (signatures p) of
    Just  _ -> Function  f t (addSignatures rest (f : sigs))
    Nothing -> if f `elem` sigs
                then Function  f t (addSignatures rest sigs)
                else Signature f (annotation t) $
                     Function f t $
                     addSignatures rest (f : sigs)
addSignatures p@(Property q t rest)  sigs =
  case lookup q (signatures p) of
    Just  _ -> Property  q t (addSignatures rest (q : sigs))
    Nothing -> if q `elem` sigs
                then Property  q t (addSignatures rest sigs)
                else Signature q (annotation t) $
                     Property q t $
                     addSignatures rest (q : sigs)
addSignatures (Signature x t rest) sigs = Signature x t $ addSignatures rest (x : sigs)
addSignatures (Data      x t rest) sigs = Data      x t $ addSignatures rest sigs
addSignatures End _ = End
