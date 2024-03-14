{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Core.Syntax
import Core.Parser
  ( parseProgram
  , report
  , Info
  )
import Analysis.TypeInferrer      (inferProgram)
import Semantics.Interpreter      (runMain)
import Semantics.REPL             (evalLoop)
import Validation.PropertyChecker (check, putStrLnRed, putStrLnGreen, redStr)

import System.Environment (getArgs)
import System.Exit        (die)
-- import System.IO          (hFlush, stdout)


-- Abbreviations
type ErrorMessage = String
type VersionInfo  = String

data Action =
    REPL          (Program Type)
  | Execute       (Program Type)
  | PropertyCheck (Program Type)
  | TypeCheck     (Program Info)
  | AST           (Program Type)
  | Version       VersionInfo
  | Fail          ErrorMessage


-- Entry point
main :: IO ()
main = getArgs >>= run . action

run :: IO Action -> IO ()
run command =
  command >>= \case
    (REPL          program) -> repl program
    (Execute       program) -> execute program
    (PropertyCheck program) -> checkProperties program
    (TypeCheck     program) -> typecheck program >>= print
    (AST           program) -> ast program
    (Version       message) -> die message
    (Fail          message) -> die message

action :: [String] -> IO Action
action ["--check", file] = PropertyCheck <$> (parse file >>= typecheck)
action ["--type",  file] = TypeCheck     <$>  parse file
action ["--ast",   file] = AST           <$> (parse file >>= typecheck)
action ["--load",  file] = REPL          <$> (parse file >>= typecheck)
action ["--version"    ] = return $ Version  versionInfo
action ["--help"       ] = return $ Fail     useInfo
action [           file] = Execute       <$> (parse file >>= typecheck)
action [ ]               = return $ REPL     End
action _                 = return $ Fail     useInfo


-- Main functions
parse :: String -> IO (Program Info)
parse file =
  do result <- parseProgram file
     case result of
       Left  problems -> putStrLnRed >> die $ redStr $ report problems
       Right program  -> return program

typecheck :: Program Info -> IO (Program Type)
typecheck = return . inferProgram

ast :: Program Type -> IO ()
ast p = print $ programAST p

repl :: Program Type -> IO ()
repl p = putStrLnGreen "Contra REPL" >> evalLoop p

execute :: Program Type -> IO ()
execute program = print $ runMain program

checkProperties :: Program Type -> IO ()
checkProperties program =
  do putStrLn "--- Contra: Checking properties ---"
     check program


-- Information about the program
versionInfo :: String
versionInfo =
  "Contra 1.0.0 (Prototype)\n\
          \Copyright (C) 2024 Sophie Bosio\n\
          \License GPL-3.0"

useInfo :: String
useInfo =
  "How to use:\n\
       \ contra          <filename>.con - Execute 'main' function in program\n\
       \ contra --check  <filename>.con - Check all properties in program\n\
       \ contra --type   <filename>.con - Type-check and print program\n\
       \ contra --load   <filename>.con - Load program into REPL\n\
       \ contra                         - Start blank interactive REPL session"

