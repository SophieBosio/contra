module Main (main) where

import Syntax
import Parser
  ( parseProgram
  , Info
  , ParsingError ( MultipleSignatures
                 , MultipleADTs
                 , MultipleFunctions
                 , MultipleProperties
                 , ParsingFailed
                 )
  )
import TypeInferrer (inferProgram)
-- import Interpreter  (normalise)

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
  command >>= \preprocessed ->
  case preprocessed of
    (REPL          program) -> repl program
    (Execute       program) -> execute program
    (PropertyCheck program) -> check program
    (TypeCheck     program) -> typecheck program >>= print
    (Version       message) -> die message
    (Fail          message) -> die message

action :: [String] -> IO Action
action ["--check", file] = PropertyCheck <$> (parse file >>= typecheck)
action ["--types", file] = TypeCheck     <$>  parse file
action ["--load",  file] = REPL          <$> (parse file >>= typecheck)
action [ ]               = return $ REPL    End
action ["--version"    ] = return $ Version versionInfo
action ["--help"       ] = return $ Fail    useInfo
action [           file] = Execute       <$> (parse file >>= typecheck)
action _                 = return $ Fail    useInfo


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
repl = const $ die "REPL is future work"

execute :: Program Type -> IO ()
execute = undefined

check :: Program Type -> IO ()
check = undefined


-- Utilities
report :: [ParsingError] -> String
report [] = ""
report ((MultipleSignatures n) : rest) =
  ("Multiple type signatures declared for function/property with name " ++ n ++ "\n")
  ++ report rest
report ((MultipleADTs n) : rest) =
  ("Multiple ADTs declared with name " ++ n ++ "\n")
  ++ report rest
report ((MultipleFunctions (n, i) : rest)) =
  let positions = ""
  in ("Multiple functions declared with name " ++ n ++ " at " ++ positions ++ "\n")
     ++ report rest
report ((MultipleProperties (n, i) : rest)) =
  let positions = ""
  in ("Multiple properties declared with name " ++ n ++ " at " ++ positions ++ "\n")
     ++ report rest
report ((ParsingFailed err) : rest) =
  ("Parsing failed: " ++ show err ++ "\n")
  ++ report rest


-- Information about the program
versionInfo :: String
versionInfo =
  "Contra 1.0.0 (Prototype)\n\
          \Copyright (C) 2024 Sophie Bosio\n\
          \License GPL-3.0"

useInfo :: String
useInfo =
  "How to use:\n\
       \ contra         <filename>.con - Execute 'main' function in program\n\
       \ contra --check <filename>.con - Check all properties in program\n\
       \ contra --types <filename>.con - Type-check program and print result\n\
       \ \n\
       \ -- FUTURE WORK: -- \n\
       \ contra --load <filename>.con  - Load program into REPL\n\
       \ contra                        - Start blank interactive REPL session"
