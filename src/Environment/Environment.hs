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


-- * Abbreviations
type Mapping      a b = a -> b
type MapsTo       a b = Mapping a b -> Mapping a b


-- * Definition
data Environment m a =
  Environment
    { function      :: F -> m (Term a)
    , property      :: P -> m (Term a)
    , definitionsIn :: [(Name, Term a)]
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
    , definitionsIn = definitions p
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
    , selector    = \(d, c) -> return $ ctrSelector p (d, c)
    , reconstruct = \(d, i) -> return $ indexReconstruct p (d, i)
    , cardinality = \d ->
        case lookup d (datatypes p) of
          Nothing -> error $ "Couldn't find data type with name '" ++ d ++ "'"
          Just cs -> return $ toInteger $ length cs
    }

