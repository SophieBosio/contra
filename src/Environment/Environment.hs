module Environment.Environment where

import Core.Syntax

import Data.Maybe (fromJust)


type Mapping      a b = a -> b
type MapsTo       a b = Mapping a b -> Mapping a b

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

