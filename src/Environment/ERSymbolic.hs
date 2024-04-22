{-

  Module      : Environment.ERSymbolic
  Description : Environment Reader Symbolic monad.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  The ERSymbolic monad is reworked from Joachim Tilsted Kristensen's
  implementation of the ERWS monad (found in Environment.ERWS). We use the same
  approach used to create an Environment Reader Writer State monad, to make
  an Environment Reader Symbolic monad.

  Symbolic is the innermost monad. Besides it, we have access to a program
  environment (i.e., the user's program text) and a Reader environment.
  Through the Environment, we can access the user's ADT definitions.

-}

module Environment.ERSymbolic where

import Core.Syntax
import Environment.Environment

import Control.Arrow
import qualified Control.Monad.Reader as Reader
import Data.SBV


-- Environment, Reader, Symbolic
newtype ERSymbolic e r a =
  ERSymbolic { coERSymbolic :: Reader.ReaderT (Environment (ERSymbolic e r) e, r) Symbolic a }

instance Monad (ERSymbolic e r) where
  return  = pure
  m >>= f = ERSymbolic $ coERSymbolic m >>= coERSymbolic . f

instance Applicative (ERSymbolic e r) where
  pure      = ERSymbolic . Reader.return
  m1 <*> m2 = m1 >>= \f -> f <$> m2

instance Functor (ERSymbolic e r) where
  fmap f = ERSymbolic . fmap f . coERSymbolic

runFormula :: ERSymbolic e r a -> Program e -> r -> Symbolic a
runFormula formula p r = Reader.runReaderT (coERSymbolic formula) (programEnvironment p, r)


-- Environment
environment :: ERSymbolic e r (Environment (ERSymbolic e r) e)
environment = ERSymbolic $ Reader.asks fst


-- Reader
local :: (r -> r) -> (ERSymbolic e r b -> ERSymbolic e r b)
local f = ERSymbolic . Reader.local (second f) . coERSymbolic

ask :: ERSymbolic e r r
ask = ERSymbolic $ Reader.asks snd


-- Symbolic
liftSymbolic :: Symbolic a -> ERSymbolic e r a
liftSymbolic = ERSymbolic . Reader.lift
