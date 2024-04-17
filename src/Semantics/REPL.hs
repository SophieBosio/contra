{-------------------------------------------------------------------------------

  Module      : Semantics.REPL
  Description : Rudimentary REPL for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  This is a rudimentary REPL (Read-Eval-Print Loop) for Contra.

  It can be used to interact with the core language and the function definitions
  in a program text. Load a program in the terminal using the
  '--load <program-name>.con' option and call functions interactively.

-------------------------------------------------------------------------------}

module Semantics.REPL where

import Core.Syntax
import Core.Parser
import Analysis.TypeInferrer
import Semantics.PartialEvaluator

import System.IO (hFlush, stdout)


-- Export
evalLoop :: Program Type -> IO ()
evalLoop p =
  do input <- readLine
     if input == ":q"
        then return ()
        else do parsed <- parseLine input
                typed  <- typeCheck parsed
                let (interpreted, residual) = eval p typed
                print interpreted
                evalLoop residual


-- Utility
readLine :: IO String
readLine = putStr "contra> "
           >> hFlush stdout
           >> getLine

parseLine :: String -> IO (Term Info)
parseLine input =
  case parseString term input of
    Left  err -> error $ "Parse error: " ++ show err
    Right t   -> return t

typeCheck :: Term a -> IO (Term Type)
typeCheck t = return $ inferTerm t

eval :: Program Type -> Term Type -> (Term Type, Program Type)
eval = partiallyEvaluate
