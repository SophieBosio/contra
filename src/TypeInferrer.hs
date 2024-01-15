{-# LANGUAGE TypeOperators #-}

module TypeInferrer where

import Syntax

import Control.Monad.RWS
import Data.Maybe        (fromMaybe)
import Data.Functor      ((<&>))


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
bind x a look y = if x == y              -- If x is already bound
                     then a              -- Update it
                     else look y         -- Bind new

hasSameTypeAs :: Term Type -> Term Type -> Annotation ()
t0 `hasSameTypeAs` t1 = tell [annotation t0 :=: annotation t1]

hasType :: Term Type-> Type -> Annotation ()
t0 `hasType` tau = tell [annotation t0 :=: tau]

