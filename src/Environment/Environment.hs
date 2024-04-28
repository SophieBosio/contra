{-

  Module      : Environment.Environment
  Description : Program environment definition.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  This file contains the type `Mapping` and the type-level operator `MapsTo`,
  which are used in:
   * Analysis.TypeInferrer
   * Environment.ERSymbolic
   * Validation.Formula

  It also contains the Program Environment, which is used in the monads in
  Environment.ERWS and Environment.ERSymbolic for convenient access to parts of
  the program text.

-}

module Environment.Environment where

import Core.Syntax

import Data.Maybe (fromJust)


type Mapping      a b = a -> b
type MapsTo       a b = Mapping a b -> Mapping a b

data Environment m a =
  Environment
    { function     :: F -> m (Term a)
    , property     :: P -> m (Term a)
    , datatype     :: C -> m D
    , fieldTypes   :: C -> m [Type]
    , constructors :: D -> m [Constructor]
    , selector     :: D -> C -> m Int
    }

programEnvironment :: Monad m => Program a -> Environment m a
programEnvironment p =
  Environment
    { function     = return . \f -> fromJust $ lookup f (functions         p)
    , property     = return . \q -> fromJust $ lookup q (properties        p)
    , datatype     = return . \c -> fromJust $ lookup c (constructorNames  p)
    , fieldTypes   = return . \c -> fromJust $ lookup c (constructorFields p)
    , constructors = return . \d -> fromJust $ lookup d (datatypes         p)
    , selector     = \d c -> return $ fromJust $ findSelector 0 c $
                                      fromJust $ lookup d (datatypes p)
    }

matches :: C -> Constructor -> Bool
matches c (Constructor d _) = c == d

findSelector :: Int -> C -> [Constructor] -> Maybe Int
findSelector _ _ [] = Nothing
findSelector i c (ctr : ctrs)
  | c `matches` ctr = Just i
  | otherwise       = findSelector (i + 1) c ctrs

