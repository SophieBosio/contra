{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Syntax
import Parser
  ( parseProgram
  , report
  , Info
  )
import TypeInferrer (inferProgram)
-- import Interpreter  (normalise)
import PropertyEngine (check)

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
    (Version       message) -> die message
    (Fail          message) -> die message

action :: [String] -> IO Action
action ["--check", file] = PropertyCheck <$> (parse file >>= typecheck)
action ["--type",  file] = TypeCheck     <$>  parse file
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
       Left  problems -> die $ report problems
       Right program  -> return program

typecheck :: Program Info -> IO (Program Type)
typecheck = return . inferProgram

repl :: Program Type -> IO ()
repl = const $ die "* REPL is future work"

execute :: Program Type -> IO ()
execute = undefined

checkProperties :: Program Type -> IO ()
checkProperties program =
  do putStrLn "CHECKING PROPERTIES: "
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
       \ \n\
       \ *-*-* FUTURE WORK: *-*-* \n\
       \ contra --load   <filename>.con - Load program into REPL\n\
       \ contra                         - Start blank interactive REPL session"
