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
import Data.Hashable (hash)
import Control.Monad (zipWithM, zipWithM_)


-- * Maximum recursion depth for ADTs and function calls
type RecursionDepth = Int

defaultRecDepth :: RecursionDepth
defaultRecDepth = 20


-- * Custom symbolic variables
data SValue =
    SUnit
  | SBoolean SBool
  | SNumber  SInteger
  | SCtr     D C [SValue]
  | SADT     X D SInteger [SValue]
  | SArgs    [SValue]
  -- SArgs represents the fabricated argument list we create when
  -- flattening function definitions into a Case-statement
  deriving Show


-- * The Formula monad
type Bindings   = Mapping X SValue
type Formula  a = ERSymbolic Type Bindings a

bind :: X -> SValue -> X `MapsTo` SValue
bind x tau look y = if x == y      -- Applying the bindings to some 'y' equal to 'x'
                       then tau    -- you should now get back 'tau'
                       else look y -- If you call it with some other 'y',
                                   -- then return the old binding for 'y'


-- * Create symbolic variables for SBV to instantiate during solving
createSymbolic :: Pattern Type -> Formula SValue
createSymbolic (Variable _ Unit')    = return SUnit
createSymbolic (Variable x Integer') =
  do sx <- lift $ sInteger x
     return $ SNumber sx
createSymbolic (Variable x Boolean') =
  do sx <- lift $ sBool x
     return $ SBoolean sx
createSymbolic (Variable x (Variable' _)) =
  do sx <- lift $ free x
     return $ SNumber sx
createSymbolic (Variable _ (TypeList [])) =
  do return $ SArgs []
createSymbolic (Variable x (TypeList ts)) =
     -- We should never be asked to create input for this type, since it's
     -- internal and not exposed to the user. However, we are able to do so.
     -- Fabricate new name for each variable by hashing <x><type-name>
     -- and appending the index of the variable type in the TypeList.
  do let names = zipWith (\tau i -> show (hash (x ++ show tau)) ++ show i)
                 ts
                 ([0..] :: [Integer])
     let ps    = zipWith Variable names ts
     sxs <- mapM createSymbolic ps
     return $ SArgs sxs
createSymbolic (Variable x (ADT adt)) =
  do env   <- environment
     si    <- lift $ sInteger $ "ADT-" ++ x
     upper <- cardinality env adt
     if upper == 1
       then do lift $ constrain $ si .== 0
               (_, c) <- reconstruct env (adt, 0)
               types  <- fieldTypes env c
               svs    <- ensureInstantiated x adt [] types
               return $ SADT x adt si svs
       else do lift $ constrain $ (si .>= 0) .&& (si .< literal upper)
               return $ SADT x adt si []
createSymbolic p = error $
     "Unexpected request to create symbolic sub-pattern '"
  ++ show p ++ "' of type '" ++ show (annotation p) ++ "'"
  ++ "\nPlease note that generating arbitrary functions is not supported."


-- * SValue (symbolic) equality
sEqual :: SValue -> SValue -> Formula SValue
sEqual  SUnit           SUnit           = return $ SBoolean sTrue
sEqual (SBoolean    b) (SBoolean     c) = return $ SBoolean (b .== c)
sEqual (SNumber     n) (SNumber      m) = return $ SBoolean (n .== m)
sEqual (SCtr adt x xs) (SCtr adt' y ys) =
  do eqs <- zipWithM sEqual xs ys
     return $ SBoolean $ sAnd $
         fromBool (adt == adt')
       : fromBool (x   == y   )
       : map truthy eqs
sEqual (SADT _ adt si xs) (SADT _ adt' sj ys) =
  do eqs <- zipWithM sEqual xs ys
     return $ SBoolean $ sAnd $
         fromBool (adt == adt')
       : (si .== sj)
       : map truthy eqs
sEqual (SCtr adt c  xs) (SADT ident adt' sj ys)
  | adt == adt' = coerce ident adt (c, sj) (xs, ys)
  | otherwise   = return $ SBoolean sFalse
sEqual (SADT ident adt si xs) (SCtr adt' c  ys)
  | adt == adt' = coerce ident adt (c, si) (ys, xs)
  | otherwise   = return $ SBoolean sFalse
sEqual (SArgs     xs) (SArgs     ys) =
  do eqs <- zipWithM sEqual xs ys
     return $ SBoolean $ sAnd $ map truthy eqs
sEqual _             _               = return $ SBoolean sFalse

truthy :: SValue -> SBool
truthy (SBoolean b) = b
truthy  SUnit       = sTrue
truthy v            = error $
  "Expected a symbolic boolean value, but got " ++ show v


-- * Coerce a symbolically created algebraic data type to be equal to a concrete one
coerce :: X -> D -> (C, SInteger) -> ([SValue], [SValue]) -> Formula SValue
coerce ident adt (c, si) (xs, ys) =
  do env    <- environment
     (_, i) <- selector env (adt, c)
     lift $ constrain $ si .== literal i
     types  <- fieldTypes env c
     ys'    <- ensureInstantiated ident adt ys types
     eqs    <- zipWithM sEqual xs ys'
     return $ SBoolean $ sAnd $
         (si .== literal i)
       : map truthy eqs


ensureInstantiated :: X -> D -> [SValue] -> [Type] -> Formula [SValue]
ensureInstantiated _     _   [ ] [   ] = return []
ensureInstantiated ident adt [ ] types = instantiate ident adt types
ensureInstantiated _     _   svs types = ensureTypeAccord svs types >> return svs

instantiate :: X -> D -> [Type] -> Formula [SValue]
instantiate ident adt types =
  do let names = map (((adt ++ "-" ++ ident ++ "-field") ++) . show) ([0..] :: [Int])
     let vars  = zipWith Variable names types
     mapM createSymbolic vars

ensureTypeAccord :: [SValue] -> [Type] -> Formula ()
ensureTypeAccord [      ] [        ] = return ()
ensureTypeAccord [      ] _          = error
  "Fatal: Symbolic algebraic data type was missing fields."
ensureTypeAccord _        [        ] = error
  "Fatal: Symbolic algebraic data type was missing fields."
ensureTypeAccord (sv:svs) (tau:taus) = match sv tau >> ensureTypeAccord svs taus
  where
    match SUnit            Unit'            = return ()
    match (SNumber      _) Integer'         = return ()
    match (SBoolean     _) Boolean'         = return ()
    match (SArgs     svs') (TypeList taus') = zipWithM_ match svs' taus'
    match (SCtr   adt _ _) (ADT adt')       | adt == adt' = return ()
    match (SADT _ adt _ _) (ADT adt')       | adt == adt' = return ()
    match sv'              tau'             = error $
      "Type mismatch occurred in equality check of constructor fields.\n\
      \Unsatisfiable constraint: '" ++ show sv' ++ "' not of expected type '"
      ++ show tau' ++ "'"


-- * SValues are 'Mergeable', meaning we can use SBV's if-then-else, called 'ite'.
instance Mergeable SValue where
  symbolicMerge = const merge

merge :: SBool -> SValue -> SValue -> SValue
merge _  SUnit        SUnit       = SUnit
merge b (SNumber  x) (SNumber  y) = SNumber  $ ite b x y
merge b (SBoolean x) (SBoolean y) = SBoolean $ ite b x y
merge b (SCtr adt x xs) (SCtr adt' y ys)
  | adt == adt' = SCtr adt (ite b x y) (mergeList b xs ys)
  | otherwise   = error $
    "Type mismatch between data type constructors '"
    ++ x ++ "' and '" ++ y ++ "'\n\
    \Of types '" ++ adt ++ "' and '" ++ adt' ++ ", respectively."
merge b (SADT x adt si xs) (SADT y adt' sj ys)
  | adt == adt' = SADT (ite b x y) adt (ite b si sj) (mergeList b xs ys)
  | otherwise   = error $
    "Type mismatch between symbolic data types '"
    ++ adt ++ "' and ' " ++ adt' ++ "'"
merge b (SCtr adt c xs) (SADT ident adt' si ys)
  | adt == adt' = ite b (SCtr adt c xs) (SADT ident adt' si ys)
  | otherwise   = error $
    "Type mismatch between concrete data type '" ++ adt ++
    "' and symbolic data type variable '" ++ ident ++
    "' with type '" ++ adt' ++ "'"
merge b (SADT ident adt si xs) (SCtr adt' c ys)
  | adt == adt' = ite b (SADT ident adt si xs) (SCtr adt' c ys)
  | otherwise   = error $
    "Type mismatch between concrete data type '" ++ adt' ++
    "' and symbolic data type variable '" ++ ident ++
    "' with type '" ++ adt ++ "'"
merge b (SArgs   xs) (SArgs   ys) = SArgs $ mergeList b xs ys
merge _ x y = error $ "Type mismatch between symbolic values '"
              ++ show x ++ "' and '" ++ show y ++ "'"

mergeList :: SBool -> [SValue] -> [SValue] -> [SValue]
mergeList sb xs ys
  | Just b <- unliteral sb = if b then xs else ys
  | otherwise              = error $ "Unable to merge arguments '"
                             ++ show xs ++ "' with '" ++ show ys ++ "'\n\
                             \Impossible to determine Boolean condition."
