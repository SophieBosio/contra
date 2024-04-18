{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}

{-------------------------------------------------------------------------------

  Module      : Validation.Formula
  Description : Formula monad and SValue definition.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  This file contains:
   - Definition of SValue - middle layer between SBV and Contra values
   - The Formula monad
   - 'bind' for creating/updating bindings from variable names to SValues
   - 'createSymbolic' for creating a symbolic variable from a Contra variable
   - `Mergeable` instance for SValues
   - Helper function 'sEqual' for comparing SValues

  The Formula monad is an instantiation of the ERSymbolic monad and keeps track
  of the following contexts:
   - Environment : Type, which is the typed program text
   - Reader      : Bindings, which are mappings from variable names to SValues
   - Symbolic    : SBV's Symbolic monad, which keeps track of solver state

-------------------------------------------------------------------------------}

module Validation.Formula where

import Core.Syntax
import Environment.Environment
import Environment.ERSymbolic

import Data.SBV
import Data.Hashable


-- Abbreviations
data SValue =
    SUnit
  | SBoolean SBool
  | SNumber  SInteger
  | SCtr     String [SValue]
  | SList    [SValue]
  deriving Show
type Bindings   = Mapping X SValue
type Formula  a = ERSymbolic Type Bindings a


-- Bind names to symbolic values
bind :: X -> SValue -> X `MapsTo` SValue
bind x tau look y = if x == y then tau else look y


-- Create symbolic variables
createSymbolic :: Pattern Type -> Formula SValue
createSymbolic (Variable _ Unit')    = return SUnit
createSymbolic (Variable x Integer') =
  do sx <- liftSymbolic $ sInteger x
     return $ SNumber sx
createSymbolic (Variable x Boolean') =
  do sx <- liftSymbolic $ sBool x
     return $ SBoolean sx
createSymbolic (Variable x (Variable' _)) =
  do sx <- liftSymbolic $ free x
     return $ SNumber sx
createSymbolic (Variable _ (Tuple [])) =
  do return $ SList []
createSymbolic (Variable x (Tuple ts)) =
     -- Fabricate new name for each variable by hashing <x><type-name>
     -- and appending the index of the variable type in the Tuple list
  do let names = zipWith (\s i -> show (hash (x ++ show s)) ++ show i)
                 ts
                 [0..(length ts)]
     let ps    = zipWith Variable names ts
     sxs <- mapM createSymbolic ps
     return $ SList sxs
createSymbolic (Variable x (t1 :->: t2)) = undefined
-- You have the name of the function and the program env
createSymbolic (Variable x (ADT t)) = undefined
--   do env <- environment
-- To generate an ADT variable, you could maybe generate a list of possible constructors + their args
createSymbolic p = error $ "Unexpected request to create symbolic sub-pattern '"
                        ++ show p ++ "'\nThis should have been handled in\n\
                           \'liftInput', not in 'createSymbolic'"


-- SValues are 'Mergeable', meaning we can use SBV's if-then-else, called 'ite'
instance Mergeable SValue where
  symbolicMerge = const merge

merge :: SBool -> SValue -> SValue -> SValue
merge _  SUnit        SUnit       = SUnit
merge b (SNumber  x) (SNumber  y) = SNumber  $ ite b x y
merge b (SBoolean x) (SBoolean y) = SBoolean $ ite b x y
merge b (SCtr  x xs) (SCtr  y ys)
  | x == y    = SCtr x $ mergeList b xs ys
  | otherwise = error $ "Type mismatch between data type constructors '"
                ++ show x ++ "' and '" ++ show y ++ "'"
merge b (SList   xs) (SList   ys) = SList $ mergeList b xs ys
merge _ x y = error $ "Type mismatch between symbolic values '"
              ++ show x ++ "' and '" ++ show y ++ "'"

mergeList :: SBool -> [SValue] -> [SValue] -> [SValue]
mergeList sb xs ys
  | Just b <- unliteral sb = if b then xs else ys
  | otherwise              = error $ "Unable to merge arguments '"
                             ++ show xs ++ "' with '" ++ show ys ++ "'"


-- SValue (symbolic) equality
sEqual :: SValue -> SValue -> SValue
sEqual  SUnit         SUnit        = SBoolean sTrue
sEqual (SBoolean  b) (SBoolean  c) = SBoolean (b .== c)
sEqual (SNumber   n) (SNumber   m) = SBoolean (n .== m)
sEqual (SCtr   x xs) (SCtr   y ys) = SBoolean $ sAnd $ fromBool (x == y)
                                     : map truthy (zipWith sEqual xs ys)
sEqual (SList    xs) (SList    ys) = SBoolean $ sAnd $ map truthy $
                                                zipWith sEqual xs ys
sEqual _             _             = SBoolean sFalse


-- Utility functions
truthy :: SValue -> SBool
truthy (SBoolean b) = b
truthy  SUnit       = sTrue
truthy v = error $ "Expected a symbolic boolean value, but got " ++ show v
