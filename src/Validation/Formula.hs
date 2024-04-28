{-

  Module      : Validation.Formula
  Description : Formula monad and SValue definition.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  The Formula file defines the abbreviations and the monad that is used in the
  PropertyChecker, Translator, and SymUnifier.

  This file contains:
   * Definition of SValue - middle layer between SBV and Contra values
   * Bindings, which is a mapping from variable names to SValues
   * The Formula monad
   * Function 'bind' to create or update Bindings
   * `Mergeable` instance for SValues
   * Helper function 'sEqual' for comparing SValues

  The Formula monad is an instantiation of the ERSymbolic monad and keeps track
  of the following contexts:
   * Environment : Type, which is the typed program text
   * Reader      : Bindings, which are mappings from variable names to SValues
   * Symbolic    : SBV's Symbolic monad, which keeps track of solver state

-}

{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}

module Validation.Formula where

import Core.Syntax
import Environment.Environment
import Environment.ERSymbolic

import Data.SBV


-- Custom symbolic variables
data SValue =
    SUnit
  | SBoolean SBool
  | SNumber  SInteger
  | SCtr     String SInteger [SValue]
  | SArgs    [SValue]
  -- SArgs represents the fabricated argument list we create when flattening
  -- function definitions into a Case-statement
  deriving Show


-- The Formula monad
type Bindings   = Mapping X SValue
type Formula  a = ERSymbolic Type Bindings a

bind :: X -> SValue -> X `MapsTo` SValue
bind x tau look y = if x == y then tau else look y


-- SValues are 'Mergeable', meaning we can use SBV's if-then-else, called 'ite'
instance Mergeable SValue where
  symbolicMerge = const merge

merge :: SBool -> SValue -> SValue -> SValue
merge _  SUnit        SUnit       = SUnit
merge b (SNumber  x) (SNumber  y) = SNumber  $ ite b x y
merge b (SBoolean x) (SBoolean y) = SBoolean $ ite b x y
merge b (SCtr  x si xs) (SCtr  y sj ys)
  | x == y     = SCtr x (ite b si sj) (mergeList b xs ys)
  | otherwise  = error $
    "Type mismatch between data type constructors '"
    ++ show x ++ "' and '" ++ show y ++ "'"
merge b (SArgs   xs) (SArgs   ys) = SArgs $ mergeList b xs ys
merge _ x y = error $ "Type mismatch between symbolic values '"
              ++ show x ++ "' and '" ++ show y ++ "'"

mergeList :: SBool -> [SValue] -> [SValue] -> [SValue]
mergeList sb xs ys
  | Just b <- unliteral sb = if b then xs else ys
  | otherwise              = error $ "Unable to merge arguments '"
                             ++ show xs ++ "' with '" ++ show ys ++ "'"


-- SValue (symbolic) equality
sEqual :: SValue -> SValue -> SValue
sEqual  SUnit          SUnit         = SBoolean sTrue
sEqual (SBoolean   b) (SBoolean   c) = SBoolean (b .== c)
sEqual (SNumber    n) (SNumber    m) = SBoolean (n .== m)
sEqual (SCtr x si xs) (SCtr y sj ys) = SBoolean $ sAnd $
                                        fromBool (x == y)
                                      : (si .== sj)
                                      : map truthy (zipWith sEqual xs ys)
sEqual (SArgs     xs) (SArgs     ys) = SBoolean $ sAnd $ map truthy $
                                                  zipWith sEqual xs ys
sEqual _             _               = SBoolean sFalse


-- Utility functions
truthy :: SValue -> SBool
truthy (SBoolean b) = b
truthy  SUnit       = sTrue
truthy v = error $ "Expected a symbolic boolean value, but got " ++ show v
