module Supercompiler where

import Data.Map
import Control.Monad.State

import Syntax
import Interpreter


-- Abbreviations
type Var       = Term Type
type FreeVars  = [Var]

type Heap = Map Var (Term Type)
data StackFrame = StackFrame
  { update      :: Var
  , apply       :: Term Type
  , scrutinise  :: Term Type
  , applyFirst  :: Term Type
  , applySecond :: Term Type
  }
type Stack     = [StackFrame]
type TermState = (Heap, Term Type, Stack)
type History   = [TermState]

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

