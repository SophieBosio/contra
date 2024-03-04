{-# LANGUAGE TypeOperators #-}

module Validation.Constrainer where

import Core.Syntax
import Environment.ERWS


-- Abbreviations
type Unknown = Term Type

data Equality = Unknown :=: Unknown
  deriving Show

type Mapping  a b = a -> b
type MapsTo   a b = Mapping a b -> Mapping a b
type Constraint   = Mapping Name Range
type Realisations = [(Name, Term Type)]

data Range =
    Undefined Type
  | Fixed
  | Unknown Unknown

type Constrainer a = ERWS a Constraint [Equality] Index


-- Export
equalise :: Program Type -> Term Type -> Term Type
equalise program prop = refine (resolve equalities) prop
  where
    (_, _, equalities) = runERWS (constrain prop) program emptyConstraints 0


-- Setup
fresh :: Constrainer a Unknown
fresh =
  do i <- get      -- Get state
     let j = i + 1
     put j         -- Update state
     return $ Pattern $ Variable (show j) $ Variable' j

bind :: Eq x => x -> a -> x `MapsTo` a
bind x a look y = if x == y
                     then a
                     else look y

equalTo :: Unknown -> Unknown -> Constrainer a ()
u1 `equalTo` u2 = tell [u1 :=: u2]

emptyConstraints :: Constraint
emptyConstraints = error . (++ " is unbound!")


-- Main functions
constrain :: Unknown -> Constrainer a Unknown
constrain = undefined
-- constrain :: Program Type -> (Term Type -> Term Type)
-- constrain program property = 


-- equalise :: Term Type -> Constrainer Unknown
-- equalise = undefined
-- equalise (Pattern p) = equalise' p
-- -- equalise (Lambda x t0 _)

-- equalise' :: Pattern a -> Constrainer Unknown
-- equalise' = undefined

resolve :: [Equality] -> Realisations
resolve = undefined

refine :: Realisations -> (Term Type -> Term Type)
refine = undefined
