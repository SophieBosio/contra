module Supercompiler where

import Data.Map hiding (split)
import Control.Monad.State

import Syntax


-- Abbreviations
type Var       = Term Type
type FreeVars  = [Var]

type Heap      = Map Var (Term Type)
type Stack     = [StackFrame]
type TermState = (Heap, Term Type, Stack)
type History   = [TermState]

emptyHistory :: History
emptyHistory = []

emptyHeap :: Heap
emptyHeap = empty

emptyTermState :: Term Type -> TermState
emptyTermState t = (emptyHeap, t, [])

data TermResult = Stop | Continue History

data StackFrame = StackFrame
  { update      :: Var
  , apply       :: Term Type
  , scrutinise  :: Term Type
  , applyFirst  :: Term Type
  , applySecond :: Term Type
  }

data Promise = Promise
  { name    :: Var
  , fvs     :: FreeVars
  , meaning :: TermState
  }

data SupercompilerState = SupercompilerState
  {
    -- inputFvs :: FreeVars
    promises :: [Promise]
  , outputs  :: [(Var, Term Type)]
  , names    :: [Var]
  }

type Supercompiler a = State SupercompilerState a


-- Export
supercompile :: Term Type -> Term Type
supercompile t = runSupercompiler (sc emptyHistory (emptyTermState t)) 


-- Main functions
runSupercompiler :: Supercompiler (Term Type) -> Term Type
runSupercompiler t = undefined

sc, sc' :: History -> TermState -> Supercompiler (Term Type)
sc  = undefined
sc' = undefined
-- sc  history = memo (sc' history)
-- sc' history state = case terminate history state of
--   Continue history' -> split (sc history') (reduce state)
--   Stop              -> split (sc history)  state


-- Monad operations
freshName :: Supercompiler Var
freshName = undefined

promise :: Promise -> Supercompiler ()
promise p = modify $ \s -> s { promises = p : promises s }

bind :: Var -> Term Type -> Supercompiler ()
bind x t = modify $ \s -> s { outputs = (x, t)  : outputs s }


-- ???
memo :: (TermState -> Supercompiler (Term Type)
      -> TermState -> Supercompiler (Term Type))
memo = undefined

match :: TermState -> TermState -> Maybe (Var -> Var)
match = undefined

freeVariables :: TermState -> FreeVars
freeVariables = undefined

rebuild :: TermState -> Term Type
rebuild = undefined


-- Evaluator
reduce :: TermState -> TermState
reduce = undefined


-- Splitting
split :: Monad m => (TermState -> m (Term Type)) -> TermState -> m (Term Type)
split = undefined


-- Termination checking
terminate :: History -> TermState -> TermResult
terminate = undefined

