module Generators where

import Syntax


-- Abbreviations
data UnifyState =
  UnifyState
    { constraints  :: Int
    , equalities   :: [(Term Type, Term Type)]
    , inequalities :: [(Term Type, Term Type)]
    , patterns     :: [(Term Type, Pattern Type)]
    , unknowns     :: [Term Type]
    , index        :: Index
    }

type Unification a = UnifyState -> Maybe (a, UnifyState)

newtype Unify a = Unify { run :: Unification a }
