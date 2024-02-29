module REPL where

import Syntax
import Parser
import TypeInferrer
import PartialEvaluator

import System.IO (hFlush, stdout)


-- Export
evalLoop :: Program Type -> IO ()
evalLoop p =
  do input <- readLine
     if input == "exit"
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