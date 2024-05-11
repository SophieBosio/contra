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

import Data.List (elemIndex)


-- * Abbreviations
type Mapping      a b = a -> b
type MapsTo       a b = Mapping a b -> Mapping a b


-- * Definition
data Environment m a =
  Environment
    { function      :: F -> m (Term a)
    , property      :: P -> m (Term a)
    , envFunctions  :: [(F, Term a)]
    , envProperties :: [(P, Term a)]
    , datatype      :: C -> m D
    , fieldTypes    :: C -> m [Type]
    , constructors  :: D -> m [Constructor]
    , selector      :: (D, C) -> m (D, Integer)
    , reconstruct   :: (D, Integer) -> m (D, C)
    , cardinality   :: D -> m Integer
    }

-- * Implementation
programEnvironment :: Monad m => Program a -> Environment m a
programEnvironment p =
  Environment
    { function = \f ->
        case lookup f (functions p) of
          Just def -> return def
          Nothing  -> error $
            "Couldn't find definition for function '" ++ f ++ "'"
    , property = \q ->
        case lookup q (properties p) of
          Just def -> return def
          Nothing  -> error $
            "Couldn't find definition for property '" ++ q ++ "'"
    , envFunctions  = functions  p
    , envProperties = properties p
    , datatype = \c ->
        case lookup c (constructorNames p) of
          Just  d -> return d
          Nothing -> error $
            "Couldn't find data type declaration for constructor '" ++ c ++ "'"
    , fieldTypes   = \c ->
        case lookup c (constructorFields p) of
          Just ts -> return ts
          Nothing -> error $ "Couldn't find constructor with name '" ++ c ++ "'"
    , constructors = \d ->
        case lookup d (datatypes p) of
          Just cs -> return cs
          Nothing -> error $ "Couldn't find data type with name '" ++ d ++ "'"
    , selector = \(d, c) ->
        case lookup d (datatypes p) of
          Nothing -> error $ "Couldn't find data type with name '" ++ d ++ "'"
          Just cs ->
            case elemIndex c (map nameOf cs) of
              Just  s -> return (d, toInteger s)
              Nothing -> error $ "Constructor '" ++ c ++
                "' not found in data type declaration of type '" ++ d ++ "'"
    , reconstruct = \(d, i) ->
        case lookup d (datatypes p) of
          Nothing   -> error $ "Couldn't find data type with name '" ++ d ++ "'"
          Just ctrs -> let cs = map nameOf ctrs
                       in  return (d, cs !! fromInteger i)
    , cardinality = \d ->
        case lookup d (datatypes p) of
          Nothing -> error $ "Couldn't find data type with name '" ++ d ++ "'"
          Just cs -> return $ toInteger $ length cs
    }

nameOf :: Constructor -> X
nameOf (Constructor x _) = x
