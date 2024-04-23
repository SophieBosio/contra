{-# LANGUAGE TypeOperators #-}

{-

  Module      : Analysis.TypeInferrer
  Description : Type inference algorithm for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  This type inference algorithm is based on De Bruijn indices and constraint
  solving.

  A constraint consists of two types that should be equal, and a string
  with the source code position of the relevant term(s) for error messages.

  Type-inference is done by annotating terms with concrete types or with
  unification variables and then adding constraints to these types. When we are
  done annotating, we solve the constraints and signal any errors.

  The Annotation monad is an instantiation of the ERWS monad and keeps track
  of the following contexts:
   * Environment: Type, which is the typed program text - including definitions
     of algebraic data types
   * Reader: Bindings, which is a mapping from variable names to types
   * Writer: [Constraint], a list of type equality constraints
   * State: Index, a fresh unification variable index

  Either a term's type judgement rule let us decide their type by the type of
  their subterms, or we generate fresh unification variables and add constraints
  to them according to the type judgement rules.

  Values (literals/canonical terms) are type-annotated directly with their
  concrete type, while Patterns and general Terms are annotated indirectly.

  Finally, we solve the constraints and replace each unification
  variable with a concrete type. If the constraints cannot be solved,
  we throw an error with a description of the unsatisfiable constraint.

  When inferring a program, we add constraints to enforce accordance between
  function/property signatures and their implementation. Additionally, we
  require that properties *must* return a Boolean value.

-}

module Analysis.TypeInferrer where

import Core.Syntax
import Environment.Environment
import Environment.ERWS

import Control.Monad (replicateM)
import Control.Arrow (second)
import Data.Foldable (foldrM, sequenceA_)

-- Abbreviations
type ConstraintError  = String
data Constraint       =
  Constraint
    { type1 :: Type
    , type2 :: Type
    , info :: ConstraintError
    }

type Bindings         = Mapping Name Type
type Annotation     a = ERWS a Bindings [Constraint] Index
type TypeSubstitution = [(Index, Type)]


-- Export
inferProgram :: Show a => Program a -> Either ConstraintError (Program Type)
inferProgram program =
  case solve constraints of
    Left err -> Left  err
    Right cs -> Right $ addSignatures [] $ refine cs <$> annotatedProgram
  where
    (annotatedProgram, _, annotationConstraints) =
      runERWS (annotateProgram program) program emptyBindings 0
    constraints =    annotationConstraints
                  ++ signatureDefinitionAccord annotatedProgram
                  ++ propertiesReturnBoolean   annotatedProgram

inferTerm :: Show a => Term a -> Term Type
inferTerm t =
  let (t', _, _) = runERWS (annotate t) End emptyBindings 0
  in  t'


-- Setup
fresh :: Annotation a Type
fresh = Variable' <$> (get >>= \i ->     -- Get current, fresh index (state)
                          put (i + 1) >> -- Increment to create next index
                          return i)      -- Return fresh

bind :: Eq x => x -> a -> x `MapsTo` a
bind x a look y = if x == y then a else look y

newConstraint :: Type -> Type -> String -> Constraint
newConstraint t1 t2 msg =
  Constraint -- tau1 should be equal to tau2
    { type1 = t1
    , type2 = t2
    , info = msg
    }

addEquality :: Type -> Type -> String -> Annotation a ()
addEquality tau1 tau2 msg = tell [newConstraint tau1 tau2 msg]

addConstraint :: Term Type -> Type -> String -> Annotation a ()
addConstraint t0 = addEquality (annotation t0)

addConstraints :: [Term Type] -> [Type] -> [String] -> Annotation a ()
addConstraints ts taus msgs = sequenceA_ (zipWith3 addConstraint ts taus msgs)

haveSameType :: Term Type -> Term Type -> String -> Annotation a ()
haveSameType t0 t1 = addConstraint t0 (annotation t1)


class HasSubstitution a where
  substitution :: Type -> Index -> (a -> a)

instance HasSubstitution Type where
  substitution t i (Variable' j) | i == j = t
  substitution t i (t0 :->:  t1) = substitution t i t0 :->: substitution t i t1
  substitution t i (TypeList ts) = TypeList $ map (substitution t i) ts
  substitution _ _ t             = t

instance HasSubstitution Constraint where
  substitution t i c =
    newConstraint (substitution t i (type1 c))
                  (substitution t i (type2 c))
                  (info c)

emptyBindings :: Bindings
emptyBindings = error . (++ " is unbound or ambiguously typed!")


-- Annotate program
annotateProgram ::Show a => Program a -> Annotation a (Program Type)
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
annotate :: Show a => Term a -> Annotation a (Term Type)
annotate (Pattern p) = annotatePattern p
annotate (TConstructor c ts _) =
  do env <- environment
     adt <- datatype env c
     ts' <- mapM annotate ts
     cs  <- constructorTypes env c
     addConstraints ts' cs (map (show . annotation) ts)
     return $ strengthenIfPossible c ts' (ADT adt)
annotate (Lambda p t _) =
  do tau <- fresh
     (p', bs) <- liftPattern (p, tau)
     t'  <- local bs $ annotate t
     return $ Lambda p' t' (tau :->: annotation t')
annotate (Let p t1 t2 _) =
  do t1' <- annotate t1
     let tau = annotation t1'
     (p', bs) <- liftPattern (p, tau)
     t2' <- local bs $ annotate t2
     return $ Let p' t1' t2' (annotation t2')
annotate (Application t1 t2 _) =
  do tau1 <- fresh
     tau2 <- fresh
     t1'  <- annotate t1
     t2'  <- annotate t2
     addConstraint t1' (tau1 :->: tau2) (show $ annotation t1)
     addConstraint t2' tau1             (show $ annotation t2)
     return $ Application t1' t2' tau2
annotate (Case t0 ts _) =
  do tau0 <- fresh
     tau1 <- fresh
     t0'  <- annotate t0
     addConstraint t0' tau0 (show $ annotation t0)
     ts'  <- mapM (\(alt, body) -> do (alt', bs) <- liftPattern (alt, tau0)
                                      body'      <- local bs $ annotate body
                                      addConstraint body' tau1 (show $ annotation body)
                                      return (alt', body')
                  ) ts
     return $ Case t0' ts' tau1
annotate (Plus t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     addConstraint t0' Integer' (show $ annotation t0)
     addConstraint t1' Integer' (show $ annotation t1)
     return $ Plus t0' t1' Integer'
annotate (Minus t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     addConstraint t0' Integer' (show $ annotation t0)
     addConstraint t1' Integer' (show $ annotation t1)
     return $ Minus t0' t1' Integer'
annotate (Lt t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     addConstraint t0' Integer' (show $ annotation t0)
     addConstraint t1' Integer' (show $ annotation t1)
     return $ Lt t0' t1' Boolean'
annotate (Gt t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     addConstraint t0' Integer' (show $ annotation t0)
     addConstraint t1' Integer' (show $ annotation t1)
     return $ Gt t0' t1' Boolean'
annotate (Equal t0 t1 _) =
  do t0' <- annotate t0
     t1' <- annotate t1
     haveSameType t0' t1' (show $ annotation t0)
     return $ Equal t0' t1' Boolean'
annotate (Not t0 _) =
  do t0' <- annotate t0
     addConstraint t0' Boolean' (show $ annotation t0)
     return $ Not t0' Boolean'
-- annotate (Rec x t0 _) =
--   do tau <- fresh
--      t0' <- local (bind x tau) $ annotate t0
--      return $ Rec x t0' $ annotation t0'

annotatePattern :: Show a => Pattern a -> Annotation a (Term Type)
annotatePattern (Value      v) = annotateValue v
annotatePattern (Variable x _) =
  do bindings <- ask
     return $ Pattern $ Variable x (bindings x)
annotatePattern (List    ps _) =
  do ts  <- mapM annotatePattern ps
     let ps' = map strengthenToPattern ts
     let tau = TypeList $ map annotation ps'
     return $ Pattern $ List ps' tau
annotatePattern (PConstructor c ps _) =
  do env <- environment
     adt <- datatype env c
     ts' <- mapM annotatePattern ps
     cs  <- constructorTypes env c
     addConstraints ts' cs (map (show . annotation) ps)
     return $ strengthenIfPossible c ts' (ADT adt)

annotateValue :: Show a => Value a -> Annotation a (Term Type)
annotateValue (Unit        _) = return $ Pattern $ Value $ Unit Unit'
annotateValue (Number    n _) = return $ Pattern $ Value $ Number n Integer'
annotateValue (Boolean   b _) = return $ Pattern $ Value $ Boolean b Boolean'
annotateValue (VConstructor c vs _) =
  do env <- environment
     adt <- datatype env c
     ts' <- mapM annotateValue vs
     cs  <- constructorTypes env c
     addConstraints ts' cs (map (show . annotation) vs)
     return $ strengthenIfPossible c ts' (ADT adt)


-- Additional contstraints
signatureDefinitionAccord :: Program Type -> [Constraint]
signatureDefinitionAccord annotatedProgram =
  [ newConstraint tau (annotation t)
        ("Mismatch between type signature and implementation for '" ++ sig ++ "'")
      | (sig, tau) <- signatures  annotatedProgram
      , (def, t)   <- definitions annotatedProgram
      , sig == def ]
  where
    definitions program = functions program ++ properties program

propertiesReturnBoolean :: Program Type -> [Constraint]
propertiesReturnBoolean annotatedProgram =
  concat
      [ [ newConstraint (returnType tau) Boolean'
          ("Property signature for '" ++ sig ++ "' must have return type Boolean")
        , newConstraint (returnType (annotation t)) Boolean'
          ("Property '" ++ prop ++ "' must return a Boolean")
        ]
      | (sig, tau) <- signatures annotatedProgram
      , (prop, t)  <- properties annotatedProgram
      , sig == prop ]


-- Resolve constraints
solve :: [Constraint] -> Either ConstraintError TypeSubstitution
solve [                 ] = Right mempty
solve (constraint : rest) =
  case (type1 constraint, type2 constraint) of
    (Unit'      , Unit'      ) -> solve rest
    (Integer'   , Integer'   ) -> solve rest
    (Boolean'   , Boolean'   ) -> solve rest
    (t0 :->:  t1, t2 :->: t3 ) -> solve $
                                  newConstraint t0 t2 (info constraint) :
                                  newConstraint t1 t3 (info constraint) :
                                  rest
    (TypeList ts, TypeList ss) ->
      solve $ zipWith (\t s -> newConstraint t s (info constraint)) ts ss ++ rest
    (ADT x1     , ADT x2     ) ->
      if   x1 /= x2
      then Left $ typeError (ADT x1) (ADT x2) (info constraint)
      else solve rest
    (Variable' i,  t1) ->
      if   i `elem` indices t1
      then (if Variable' i /= t1
               then Left $ typeError (Variable' i) t1 (info constraint)
               else solve rest)
      else do c <- solve (substitution t1 i <$> rest)
              return $ (i, t1) : c
    (t0, Variable' i) ->
      if   i `elem` indices t0
      then (if Variable' i /= t0
               then Left $ typeError t0 (Variable' i) (info constraint)
               else solve rest)
      else do c <- solve (substitution t0 i <$> rest)
              return $ (i, t0) : c
    (tau1, tau2) -> Left $ typeError tau1 tau2 (info constraint)

refine :: TypeSubstitution -> (Type -> Type)
refine [            ] t                      = t
refine s@((i, u) : _) (Variable' j) | i == j = refine s u
refine (_     : rest) (Variable' j)          = refine rest (Variable' j)
refine _              Unit'                  = Unit'
refine _              Integer'               = Integer'
refine _              Boolean'               = Boolean'
refine s              (tau0 :->: tau1)       = refine s tau0 :->: refine s tau1
refine _              (ADT name)             = ADT name
refine s              (TypeList ts)          = TypeList $ map (refine s) ts


-- Lifting (binding) variables
liftPattern :: Show a =>
               (Pattern a, Type) ->
               Annotation a (Pattern Type, Bindings -> Bindings)
liftPattern (Variable x _, tau) = return (Variable x tau, bind x tau)
liftPattern (Value v, tau) =
  do t' <- annotateValue v
     addConstraint t' tau (show $ annotation v)
     let p' = strengthenToPattern t'
     return (p', id)
liftPattern (PConstructor c ps a, tau) =
  do env <- environment
     adt <- datatype env c
     cs  <- constructorTypes env c
     addEquality tau (ADT adt) (show a)
     (ps', bs) <- foldrM liftMany ([], id) (zip ps cs)
     return (PConstructor c ps' tau, bs)
liftPattern (List ps a, tau) =
  do xs <- replicateM (length ps) fresh
     (ps', bs) <- foldrM liftMany ([], id) (zip ps xs)
     addEquality tau (TypeList xs) (show a)
     return (List ps' tau, bs)

liftMany :: Show a =>
            (Pattern a, Type) ->
            ([Pattern Type], Bindings -> Bindings) ->
            Annotation a ([Pattern Type], Bindings -> Bindings)
liftMany (p, tau) (ps, bs) =
  do (p', b) <- liftPattern (p, tau)
     return (ps ++ [p'], bs . b)


liftFreeVariables :: [(Name, Type)] -> (Bindings -> Bindings)
liftFreeVariables [             ] bs = bs
liftFreeVariables ((x, t) : rest) bs = bind x t $ liftFreeVariables rest bs


-- Alpha renaming
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
    increment (TypeList       ts) = TypeList $ map increment ts
    increment t'               = t'

alphaADT :: Index -> [Constructor] -> (Index, [Constructor])
alphaADT i = foldr (\c (j, k) -> second (: k) (alphaDef j c)) (i, [])

alphaDef :: Index -> Constructor -> (Index, Constructor)
alphaDef i (Constructor c cs) = second (Constructor c)
                                  (foldr (\t (j, ts) ->
                                          second (: ts) (alpha j t)) (i, []) cs)


-- Utility functions
indices :: Type -> [Index]
indices (Variable' i) = return i
indices (t0  :->: t1) = indices t0 ++ indices t1
indices (TypeList ts) = concatMap indices ts
indices _             = mempty

returnType :: Type -> Type
returnType (_ :->: t2) = returnType t2
returnType t           = t

addSignatures :: [Name] -> Program Type -> Program Type
addSignatures sigs p@(Function f t rest) =
  case lookup f (signatures p) of
    Just  _ -> Function  f t (addSignatures (f : sigs) rest)
    Nothing -> if f `elem` sigs
                then Function  f t (addSignatures sigs rest)
                else Signature f (annotation t) $
                     Function f t $
                     addSignatures (f : sigs) rest
addSignatures sigs p@(Property q t rest) =
  case lookup q (signatures p) of
    Just  _ -> Property  q t (addSignatures (q : sigs) rest)
    Nothing -> if q `elem` sigs
                then Property  q t (addSignatures sigs rest)
                else Signature q (annotation t) $
                     Property q t $
                     addSignatures (q : sigs) rest
addSignatures sigs (Signature x t rest) = Signature x t $ addSignatures (x : sigs) rest
addSignatures sigs (Data      x t rest) = Data      x t $ addSignatures sigs rest
addSignatures _ End = End


-- Error messages
typeError :: Type -> Type -> String -> ConstraintError
typeError t1 t2 msg =    "Type error: Expected term of type '" ++ show t2
                      ++ "' but got term of type '" ++ show t1 ++ "'\n"
                      ++ unquote msg
  where
    unquote ""            = ""
    unquote ('\"' : rest) = unquote rest
    unquote (x    : rest) = x : unquote rest
