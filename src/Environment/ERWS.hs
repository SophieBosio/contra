module Environment.ERWS where

-- The author of the monad in this file is Joachim Tilsted Kristensen,
-- and all credit for this file should go to him.

import Core.Syntax

import Data.Maybe
import Control.Arrow
import qualified Control.Monad.RWS as RWS


data Environment m a =
  Environment
    { function         :: F -> m (Term a)
    , property         :: P -> m (Term a)
    , datatype         :: C -> m T
    , constructors     :: T -> m [Constructor]
    , constructorTypes :: C -> m [Type]
    }

programEnvironment :: Monad m => Program a -> Environment m a
programEnvironment p =
  Environment
    { function         = return . \f -> fromJust $ lookup f (functions        p)
    , property         = return . \q -> fromJust $ lookup q (properties       p)
    , datatype         = return . \c -> fromJust $ lookup c (constructorNames p)
    , constructors     = return . \t -> fromJust $ lookup t (datatypes        p)
    , constructorTypes = return . \c -> fromJust $ lookup c (constructorArgs  p)
    }

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

