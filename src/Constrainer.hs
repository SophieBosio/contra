{-# LANGUAGE TypeOperators #-}

module Constrainer where

import Syntax
import Control.Monad.RWS


-- Abbreviations
type Unknown = Term Type

data Constraint = Unknown :=: Unknown
  deriving Show

type Mapping a b = a -> b
type MapsTo  a b = Mapping a b -> Mapping a b
type Environment = Mapping Name Unknown

data Range =
    Undefined Type
  | Fixed
  | Unknown Unknown


-- Constrainer Monad
type Constrainer = RWS Environment [Constraint] Index

fresh :: Constrainer Unknown
fresh =
  do i <- get      -- Get state
     let j = i + 1
     put j         -- Update state
     return $ Pattern $ Variable (show j) $ Variable' j

bind :: Eq x => x -> a -> x `MapsTo` a
bind x a look y = if x == y
                     then a
                     else look y

equalTo :: Unknown -> Unknown -> Constrainer ()
u1 `equalTo` u2 = tell [u1 :=: u2]


-- Main functions
equalise :: Term Type -> Constrainer Unknown
equalise (Pattern p) = equalise' p
-- equalise (Lambda x t0 _)

equalise' :: Pattern a -> Constrainer Unknown
equalise' = undefined
