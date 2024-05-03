{-

  Module      : Semantics.REPL
  Description : Rudimentary REPL for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  This is a rudimentary REPL (Read-Eval-Print Loop) for Contra.

  It can be used to interact with the core language and the function definitions
  in a program text. After starting the REPL, load a program in the terminal
  with ':l <filename.con>' and start calling functions interactively.

-}

module Semantics.REPL where

import Core.Syntax
import Core.Parser hiding (program)
import Analysis.TypeInferrer
import Semantics.PartialEvaluator

import System.IO   (hFlush, stdout)
import System.Exit (die)


-- Export
loop :: Program Type -> IO ()
loop p =
  do input <- readLine
     case input of
       ":q"                -> return ()
       (':':'l':' ': file) -> do program <- loadProgram file
                                 putStrLn $ "Loaded file " ++ show file
                                 loop program
       command             -> do parsed <- parseLine command
                                 typed  <- typeCheck parsed
                                 let (interpreted, residual) = eval p typed
                                 print interpreted
                                 loop residual


-- Utility
loadProgram :: String -> IO (Program Type)
loadProgram file = parse file >>= typecheck

parse :: String -> IO (Program String)
parse file =
  do result <- parseProgram file
     case result of
       Left  problems -> die $ redStr $ report problems
       Right program  -> return program

typecheck :: Program String -> IO (Program Type)
typecheck program =
  case inferProgram program of
    Left err -> die $ redStr err
    Right tp -> return tp

readLine :: IO String
readLine = putStr "contra> "
           >> hFlush stdout
           >> getLine

parseLine :: String -> IO (Term Info)
parseLine input =
  case parseString term input of
    Left  err -> error $ "Parse error: " ++ show err
    Right t   -> return t

typeCheck :: Show a => Term a -> IO (Term Type)
typeCheck t = return $ inferTerm t

eval :: Program Type -> Term Type -> (Term Type, Program Type)
eval = partiallyEvaluate
