module Interpreter where

import Syntax

import Control.Monad.Reader


-- Abbreviation
type Runtime a = Reader (Program a)

-- Export
interpret :: Show a => Program a -> (Term a -> Term a)
interpret p t = runReader (evaluate t) p


-- Main function
evaluate :: Show a => Term a -> Runtime a (Term a)
evaluate = undefined


-- Utility functions
substitute = undefined

