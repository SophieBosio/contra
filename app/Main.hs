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
import Validation.PropertyChecker (check, redStr)

import System.Environment (getArgs)
import System.Exit        (die)


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
       Left  problems -> die $ redStr $ report problems
       Right program  -> return program

typecheck :: Program Info -> IO (Program Type)
typecheck program =
  case inferProgram program of
    Left err -> die $ redStr err
    Right tp -> return tp

ast :: Program Type -> IO ()
ast program = print $ programAST program

repl :: Program Type -> IO ()
repl program =
  do putStrLn "✦ Contra REPL! ✦\n"
     evalLoop program

execute :: Program Type -> IO ()
execute program =
  do putStrLn "✦ Contra ✦\n"
     print (runMain program)

checkProperties :: Program Type -> IO ()
checkProperties program =
  do putStrLn "✦ Contra: Checking properties ✦\n"
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
       \ contra --ast    <filename>.con - Type-check and print abstract syntax-tree\n\
       \ contra --load   <filename>.con - Load program into REPL\n\
       \ contra                         - Start blank interactive REPL session\n\
  \Exit REPL with ':q'"

