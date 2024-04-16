{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}

module Validation.Formula where

import Core.Syntax
import Environment.Environment
import Environment.ERSymbolic

import Data.SBV


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


-- Symbolic equality
truthy :: SValue -> SBool
truthy (SBoolean b) = b
truthy v = error $ "Expected a symbolic boolean value, but got " ++ show v

sEqual :: SValue -> SValue -> SValue
sEqual  SUnit         SUnit        = SBoolean sTrue
sEqual (SBoolean  b) (SBoolean  c) = SBoolean (b .== c)
sEqual (SNumber   n) (SNumber   m) = SBoolean (n .== m)
sEqual (SCtr   x xs) (SCtr   y ys) = SBoolean $ sAnd $ fromBool (x == y)
                                     : map truthy (zipWith sEqual xs ys)
sEqual (SList    xs) (SList    ys) = SBoolean $ sAnd $ map truthy $
                                                zipWith sEqual xs ys
sEqual _             _             = SBoolean sFalse


-- SValues are 'Mergeable'
-- This means we can use SBV's if-then-else implementation, called 'ite'
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


-- Monad operations: Binding variables and generating fresh symbolic variables
bind :: X -> SValue -> X `MapsTo` SValue
bind x tau look y = if x == y then tau else look y

fresh :: X -> Type -> Formula SValue
fresh _ Unit'    = return SUnit
fresh x Integer' =
  do sx <- liftSymbolic $ sInteger x
     return $ SNumber sx
fresh x Boolean' =
  do sx <- liftSymbolic $ sBool x
     return $ SBoolean sx
fresh x (Variable' _) =
  do sx <- liftSymbolic $ free x
     return $ SNumber sx
fresh x (Args ts) = undefined
--   do sxs <- mapM fresh ts
--      return $ SList sxs
fresh x (t1 :->: t2) = undefined
fresh x (ADT t) = undefined
--   do env <- environment
-- To generate a fresh ADT variable, you could maybe generate a list of possible constructors + their args
