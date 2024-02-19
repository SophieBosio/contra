{-# LANGUAGE LambdaCase #-}

module PropertyEngine where

import Syntax
import Interpreter (normalise)

import System.IO             (hFlush, stdout)
-- import Data.SBV

import Test.Tasty.QuickCheck
  ( Gen
  , generate
  -- , oneof
  -- , frequency
  -- , arbitrary
  -- , elements
  -- , suchThat
  -- , sized
  )


-- Abbrevations


-- Export
check :: Program Type -> Int -> (P, Term Type) -> IO ()
check prog n (name, prop) =
  do putStr $ "Testing " ++ name ++ " ❯ "
     let gen  = generateGenerator prog prop
     let eval = normalise prog
     runTests gen eval prop n n


-- Main functions
runTests :: Gen (Maybe (Term Type)) -> (Term Type -> Value Type)
         -> Term Type -> Int -> Int -> IO ()
runTests _   _    _    0 total = putStrLn " ✓ OK"
runTests gen eval prop n total =
  generate gen >>= \case
    Nothing -> putStrLn "No counterexamples found!"
    Just  t -> case eval t of
      Boolean True _ -> putStr "∘" >> hFlush stdout >> runTests gen eval prop (n - 1) total
      _              -> do
        putStrLn " ✱ FAIL"
        putStr "Counterexample: "
        print t
        putStrLn $ "\nAfter " ++ show (total - n) ++ " tests."

generateGenerator :: Program Type -> Term Type -> Gen (Maybe (Term Type))
generateGenerator = undefined
