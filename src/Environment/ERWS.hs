{-

  Module      : Environment.ERWS
  Description : Environment Reader Writer State monad.
  Copyright   : (c) 2022 Joachim Tilsted Kristensen
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  This implementation is by Joachim Tilsted Kristensen.

  The Environment Reader Writer State monad transforms the usual RWS monad
  and adds a program environment (Environment.Environment), which gives us
  convenient access to parts of the user-written program text. Importantly,
  we can access the user's ADT definitions.

-}

module Environment.ERWS where

import Core.Syntax
import Environment.Environment

import Control.Arrow
import qualified Control.Monad.RWS as RWS


-- Environment Reader Writer State monad
newtype ERWS e r w s a =
  ERWS { coERWS :: RWS.RWS (Environment (ERWS e r w s) e, r) w s a }

instance Monoid w => Monad (ERWS e r w s) where
  return  = pure
  m >>= f = ERWS $ coERWS m >>= coERWS . f

instance Monoid w => Applicative (ERWS e r w s) where
  pure = ERWS . RWS.return
  e0 <*> e1 = e0 >>= \f -> f <$> e1

instance Monoid w => Functor (ERWS e r w s) where
  fmap f = ERWS . fmap f . coERWS

runERWS :: Monoid w => ERWS e r w s a -> Program e -> r -> s -> (a, s, w)
runERWS erws p r = RWS.runRWS (coERWS erws) (programEnvironment p, r)

-- Environment.
environment :: Monoid w => ERWS e r w s (Environment (ERWS e r w s) e)
environment = ERWS $ fst <$> RWS.ask

-- Reader.
local :: Monoid w => (r -> r) -> (ERWS e r w s b -> ERWS e r w s b)
local f = ERWS . RWS.local (second f) . coERWS

ask :: Monoid w => ERWS e r w s r
ask = ERWS $ snd <$> RWS.ask

-- Writer.
tell :: Monoid w => w -> ERWS e r w s ()
tell = ERWS . RWS.tell

-- State.
put :: Monoid w => s -> ERWS e r w s ()
put = ERWS . RWS.put

get :: Monoid w => ERWS e r w s s
get = ERWS RWS.get

modify :: Monoid w => (s -> s) -> ERWS e r w s ()
modify f = ERWS $ RWS.modify f

-- "Getter".
infixl 2 <?>

(<?>) :: Monad m => m (a -> m b) -> (a -> m b)
mf <?> a = mf >>= \f -> f a

