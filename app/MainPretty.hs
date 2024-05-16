{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Core.Syntax
import Core.Parser
  ( parseProgram
  , report
  )
import Analysis.TypeInferrer      (inferProgram)
import Semantics.Interpreter      (runMain)
import Semantics.REPL             (loop)
import Validation.PropertyChecker (check)
import Validation.Formula         (defaultRecDepth)

import System.Environment (getArgs)
import System.Exit        (die)


-- Abbreviations
type ErrorMessage = String
type VersionInfo  = String

data Action =
    REPL                     (Program Type)
  | Execute                  (Program Type)
  | PropertyCheckDefault     (Program Type)
  | PropertyCheckCustom  Int (Program Type)
  | TypeCheck                (Program String)
  | Version                  VersionInfo
  | Fail                     ErrorMessage


-- Entry point
main :: IO ()
main = getArgs >>= run . action

run :: IO Action -> IO ()
run command =
  command >>= \case
    (REPL                   program) -> repl program
    (Execute                program) -> execute program
    (PropertyCheckDefault   program) -> checkProperties program defaultRecDepth
    (PropertyCheckCustom  n program) -> checkProperties program n
    (TypeCheck              program) -> typeCheck program >>= print
    (Version                message) -> die message
    (Fail                   message) -> die message

action :: [String] -> IO Action
action ["--check",    file] = PropertyCheckDefault
                              <$> (parse file >>= typeCheck)
action ["--check", n, file] = PropertyCheckCustom (read n)
                              <$> (parse file >>= typeCheck)
action ["--type",     file] = TypeCheck     <$>  parse file
action ["--version"       ] = return $ Version  versionInfo
action ["--help"          ] = return $ Fail     useInfo
action [              file] = Execute       <$> (parse file >>= typeCheck)
action [ ]                  = return $ REPL     End
action _                    = return $ Fail     useInfo


-- Main functions
parse :: String -> IO (Program String)
parse file =
  do result <- parseProgram file
     case result of
       Left  problems -> die $ redStr $ report problems
       Right program  -> return program

typeCheck :: Program String -> IO (Program Type)
typeCheck program =
  case inferProgram program of
    Left err -> die $ redStr err
    Right tp -> return tp

repl :: Program Type -> IO ()
repl program =
  do putStrLn "✦ Started the Contra REPL! ✦\n"
     loop program

execute :: Program Type -> IO ()
execute program =
  do putStrLn "✦ Contra ✦\n"
     print (runMain program)

checkProperties :: Program Type -> Int -> IO ()
checkProperties program depth =
  do let pretty = True
     let depthInfo = if depth == defaultRecDepth
           then "default recursion depth"
           else "max. recursion depth set to " ++ show depth
     putStrLn $ "✦ Contra: Checking properties with " ++ depthInfo ++ " ✦\n"
     check pretty depth program


-- Information about the program
versionInfo :: String
versionInfo =
  "Contra 1.0.0 (Prototype)\n\
          \Copyright (C) 2024 Sophie Bosio\n\
          \License GPL-3.0"

useInfo :: String
useInfo =
  "How to use:\n\
       \ contra --check   <filename>.con - Check all properties in program\n\
       \ contra --check n <filename.con> - Check properties with max. recursion depth 'n'\n\
       \ contra --type    <filename>.con - Type-check and print program\n\
       \ contra           <filename>.con - Execute 'main' function in program\n\
       \ contra                          - Start an interactive REPL session\n\
  \Load file into REPL with ':l <filename.con>'\n\
  \Exit REPL with ':q'"

