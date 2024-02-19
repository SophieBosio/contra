{-# LANGUAGE TypeOperators #-}

module TypeInferrer where

import Syntax

import Control.Monad.RWS
import Control.Arrow (second)
import Data.Maybe (fromMaybe)

-- Abbreviations
data Constraint = Type :=: Type
  deriving Show

type Mapping  a b = a -> b
type MapsTo   a b = Mapping a b -> Mapping a b
type Environment  = Mapping Name Type
type Annotation   = RWS Environment [Constraint] Index
type Substitution = [(Index, Type)]


-- Export
inferProgram :: Program a -> Program Type
inferProgram program = refine (resolveConstraints constraints) <$> annotatedProgram
  where
    definitions  prog = functions  prog ++ properties prog
    constraints = annotationConstraints ++ signatureDefinitionAccord
    (annotatedProgram, _, annotationConstraints) =
      runRWS (annotateProgram program) emptyEnvironment 0
    signatureDefinitionAccord =
      [ t' :=: annotation t'' | (x, t')  <- signatures  annotatedProgram
                              , (y, t'') <- definitions annotatedProgram
                              , x == y ]


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
  substitute t i (Variable' j) | i == j = t
  substitute t i (t0 :->:  t1) = substitute t i t0 :->: substitute t i t1
  substitute _ _ t             = t

instance HasSubstitution Constraint where
  substitute t i (t0 :=: t1) = substitute t i t0 :=: substitute t i t1

emptyEnvironment :: Environment
emptyEnvironment = error . (++ " is unbound!")


-- Annotate program
-- TODO: In thesis text, note Joachim's comment:
         -- This forces that all recursive functions must have type
         -- declarations. It also forces the ML style monomorphism
         -- constraint on recursive things at top-level. This may be be more
         -- restrictive than what we want, but on the other hand, it was
         -- easy to implement {^_^}.
annotateProgram :: Program a -> Annotation (Program Type)
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
     return $ Property p def' rest'
annotateProgram End = return End


-- Annotate terms
annotate :: Term a -> Annotation (Term Type)
annotate (Pattern     p) = annotatePattern p
annotate (TConstructor c ts _) =
  do tau <- fresh
     ts' <- local (bind c tau) $ mapM annotate ts
     if all isPattern ts'
       then let ps = map strengthenToPattern ts'
            in  return $ Pattern $ PConstructor c ps tau
       else return $ TConstructor c ts' tau
annotate (Lambda x t0 _) =
  do tau <- fresh
     t0' <- local (bind x tau) $ annotate t0
     return $ Lambda x t0' (tau :->: annotation t0')
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
-- annotate (Rec x t0 _) =
--   do tau <- fresh
--      t0' <- local (bind x tau) $ annotate t0
--      return $ Rec x t0' $ annotation t0'

annotatePattern :: Pattern a -> Annotation (Term Type)
annotatePattern (Value      v) = annotateValue v
annotatePattern (Variable x _) =
  do env <- ask
     return $ Pattern $ Variable x $ env x
annotatePattern (PConstructor c ps _) =
  do tau <- fresh
     ts  <- local (bind c tau) $ mapM annotatePattern ps
     ps' <- mapM (return . strengthenToPattern) ts
     if all canonical ps'
       then let vs' = map strengthenToValue ps'
            in  return $ Pattern $ Value $ VConstructor c vs' tau
       else return $ Pattern $ PConstructor c ps' tau

annotateValue :: Value a -> Annotation (Term Type)
annotateValue (Unit        _) = return $ Pattern $ Value $ Unit Unit'
annotateValue (Number    n _) = return $ Pattern $ Value $ Number n Integer'
annotateValue (Boolean   b _) = return $ Pattern $ Value $ Boolean b Boolean'
annotateValue (VConstructor c vs _) =
  do tau <- fresh
     ts  <- local (bind c tau) $ mapM annotateValue vs
     vs' <- mapM (return . strengthenToValue . strengthenToPattern) ts
     return $ Pattern $ Value $ VConstructor c vs' tau


-- Resolve constraints
resolveConstraints :: [Constraint] -> Substitution
resolveConstraints = fromMaybe (error "Type error occurred") . solve

solve :: [Constraint] -> Maybe Substitution
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
      else do c <- solve (substitute t1 i <$> rest)
              return $ (i, t1) : c
    t0 :=: Variable' i ->
      if   i `elem` indices t0
      then (if Variable' i /= t0 then Nothing else solve rest)
      else do c <- solve (substitute t0 i <$> rest)
              return $ (i, t0) : c
    _                               -> error $ show constraint

refine :: Substitution -> (Type -> Type)
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

freeVariables :: Pattern a -> [Name]
freeVariables (Value             _) = mempty
freeVariables (Variable     x    _) = return x
freeVariables (PConstructor x ps _) =
  [ y | y <- foldr (\p acc -> acc <> freeVariables p) mempty ps, x /= y ]

liftFreeVariables :: [(Name, Type)] -> (Environment -> Environment)
liftFreeVariables [              ] e = e
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


alphaADT :: Index -> ([(C, [Type])] -> (Index, [(C, [Type])]))
alphaADT i =
  foldr (\def (j, defs') -> second ((defs' ++) . return) (alphaDefs j def))
  (i, [])

alphaDefs :: Index -> ((C, [Type]) -> (Index, (C, [Type])))
alphaDefs i (c, ts) =
  let (k, ts') = foldr (\tau (j, taus) -> second ((taus ++) . return)
                         (alpha j tau)) (i, []) ts
  in  (k, (c, ts'))
