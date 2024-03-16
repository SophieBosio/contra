module Environment.ERSym where

import Core.Syntax
import Environment.Environment

import Data.Maybe
import Control.Arrow
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Reader.Class as RC
import Data.SBV


-- Environment, Reader, Symbolic
newtype ERSym e r a =
  ERSym { coERSym :: Reader.ReaderT (Environment (ERSym e r) e, r) Symbolic a }

instance Monad (ERSym e r) where
  return = pure
  (>>=) = undefined

instance Applicative (ERSym e r) where
  pure = undefined
  (<*>) = undefined

instance Functor (ERSym e r) where
  fmap = undefined

runFormula :: ERSym e r a -> Program e -> r -> Symbolic a
runFormula formula p r = Reader.runReaderT (coERSym formula) (programEnvironment p, r)


-- Environment
environment :: ERSym e r (Environment (ERSym e r) e)
environment = ERSym $ Reader.asks fst


-- Reader
local :: (r -> r) -> (ERSym e r b -> ERSym e r b)
local f = ERSym . Reader.local (second f) . coERSym

ask :: ERSym e r r
ask = ERSym $ Reader.asks snd

