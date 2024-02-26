{-# LANGUAGE TypeOperators #-}

module Constrainer where

import Syntax
import Control.Monad.RWS


-- Abbreviations
type Unknown = Term Type

data Equality = Unknown :=: Unknown
  deriving Show

type Mapping   a b = a -> b
type MapsTo    a b = Mapping a b -> Mapping a b
type Constraint    = Mapping Name Range
type Instantiation = [(Name, Value Type)]

data Range =
    Undefined Type
  | Fixed
  | Unknown Unknown

type Constrainer = RWS Constraint [Equality] Index


-- Export
constraints :: Program Type -> (P, Term Type) -> Constraint
constraints program = resolve generatedConstraints
  where
    --  r w s a -> (a, s, w)
    (_, _, generatedConstraints) = runRWS (constrainProgram program) emptyEnvironment 0


-- Setup
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

emptyEnvironment :: Constraint
emptyEnvironment = error . (++ " is unbound!")


-- Main functions
constrainProgram :: Program Type -> Constrainer (Program Type)
constrainProgram = undefined

constrain :: Unknown -> Constrainer Unknown
constrain = undefined
-- constrain :: Program Type -> (Term Type -> Term Type)
-- constrain program property = 


-- equalise :: Term Type -> Constrainer Unknown
-- equalise = undefined
-- equalise (Pattern p) = equalise' p
-- -- equalise (Lambda x t0 _)

-- equalise' :: Pattern a -> Constrainer Unknown
-- equalise' = undefined

resolve :: [Equality] -> (P, Term Type) -> Constraint
resolve = undefined
