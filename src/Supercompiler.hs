module Supercompiler where

import Data.Map
import Control.Monad.State

import Syntax
import Interpreter


-- Abbreviations
type Var       = Term Type
type FreeVars  = [Var]

type Heap = Map Var (Term Type)
type Stack     = [StackFrame]
type TermState = (Heap, Term Type, Stack)
type History   = [TermState]

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
  { inputFvs :: FreeVars
  , promises :: [Promise]
  , outputs  :: [(Var, Term Type)]
  , names    :: [Var]
  }

type Supercompiler a = State SupercompilerState a


-- Export
supercompile :: Term Type -> Term Type
supercompile = undefined

sc :: History -> TermState -> Supercompiler (Term Type)
sc = undefined


-- Monad operations
freshName :: Supercompiler Var
freshName = undefined

promise :: Promise -> Supercompiler ()
promise = undefined

bind :: Var -> Term Type -> Supercompiler ()
bind = undefined

memo :: (TermState -> Supercompiler (Term Type)
      -> TermState -> Supercompiler (Term Type))
memo = undefined

match :: TermState -> TermState -> Maybe (Var -> Var)
match = undefined


-- Evaluator
reduce :: TermState -> TermState
reduce = undefined


-- Splitter
split :: Monad m => (TermState -> m (Term Type)) -> TermState -> m (Term Type)
split = undefined


-- Termination checking
emptyHistory :: History
emptyHistory = []

terminate :: History -> TermState -> TermResult
terminate = undefined
