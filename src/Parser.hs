module Parser where

import Syntax hiding (parens)

import Text.Parsec
import Text.Parsec.Pos (newPos)
import Control.Monad (void, when)
import Data.Functor ((<&>))
import Data.List (nub, (\\))


-- Abbreviations
type Source = String
type Parser = Parsec Source ()
type Info   = (SourcePos, SourcePos)

data ParsingError =
    MultipleSignatures    X
  | MultipleADTs          X
  | MultipleFunctions    (X, Info)
  | MultipleProperties   (X, Info)
  | ParsingFailed        ParseError
  deriving Show

reportErrors :: Program Info -> [ParsingError]
reportErrors p =
     [ MultipleSignatures  n         | n <- sigs  \\ nub sigs  ]
  ++ [ MultipleADTs        n         | n <- adts  \\ nub adts  ]
  ++ [ MultipleFunctions  (n, pos n) | n <- funcs \\ nub funcs ]
  ++ [ MultipleProperties (n, pos n) | n <- props \\ nub props ]
  where
    sigs  = fst <$> signatures p
    adts  = fst <$> datatypes  p
    funcs = fst <$> functions  p
    props = fst <$> properties p
    pos n =
      maybe
      (newPos "unknown parse error" 0 0, 
       newPos "unknown parse error" 0 0)
      annotation (lookup n (functions p ++ properties p))


-- Export
parseProgram :: Source -> IO (Either [ParsingError] (Program Info))
parseProgram path =
  do src <- readFile path
     return $
       case runParser (many whitespace >> program) () path src of
         (Left   err) -> Left $ return $ ParsingFailed err
         (Right code) ->
           case reportErrors code of
             [ ] -> return code
             _   -> Left $ reportErrors code

parseString :: Parser a -> String -> Either ParseError a
parseString p = runParser p () "<error>"
    

-- Language basics
comment :: Parser ()
comment = void $ lexeme $ symbol "--" >> many (noneOf "\n")

reservedKeywords :: [String]
reservedKeywords =
  [ "if"
  , "then"
  , "else"
  , "case"
  , "of"
  , "let"
  , "in"
  , "adt"
  , "not"
  -- , "rec"
  ]

identHead :: Parser Char
identHead = lower <|> underscore

identTail :: Parser Char
identTail = try $ choice [ letter, digit, dash, underscore ]

identifier :: Parser String
identifier = try $
  do name <- (:) <$> identHead <*> many identTail
     when (reserved name) $ fail $ "Error: Reserved keyword " ++ name
     lexeme $ return name

constructorName :: Parser String
constructorName = try $
  do name <- (:) <$> upper <*> many identTail
     lexeme $ return name

keyword :: String -> Parser ()
keyword s = try $ void $ lexeme $ string s >> notFollowedBy identTail


-- Types
type' :: Parser Type
type' = choice
  [ try $ partialArrowType type'
  , simpleType
  ]

simpleType :: Parser Type
simpleType = choice
  [ Unit'     <$  unit
  , Integer'  <$  symbol "Integer"
  , Boolean'  <$  symbol "Boolean"
  , Variable' <$> number
  , ADT       <$> constructorName
  , parens type'
  ]

partialArrowType :: Parser Type -> Parser Type
partialArrowType retType =
  do argType <- simpleType
     arrow >> (argType :->:) <$> retType


-- Values
number :: Parser Integer
number = option id (symbol "-" >> return negate) <*> digits
  where digits = lexeme $ read <$> many1 digit

boolean :: Parser Bool
boolean = choice
  [ symbol "True"  >> return True
  , symbol "False" >> return False
  ]

unit :: Parser ()
unit = void $ symbol "Unit"

value :: Parser (Value Info)
value = choice $
  parens value :
  map info
    [ Unit         <$  unit
    , number       <&> Number
    , boolean      <&> Boolean
    ]


-- Patterns
pattern' :: Parser (Pattern Info)
pattern' = choice $
  [ parens pattern'
  , Value <$> value
  , info $ identifier <&> Variable
  ]

-- Terms
term :: Parser (Term Info)
term = choice $
  parens term :
  chainl1 patternTerm operator :
  map try
    [ caseStatement
    , desugaredIf
    , termConstructor
    ]
  ++
  map info
    [ symbol  "\\"  >> Lambda <$> identifier <*> (arrow >> term)
    , keyword "not" >> Not    <$> term
    , keyword "let" >> Let    <$> identifier <*>
                       (symbol "=" >> term)  <*> (symbol "in" >> term)
    -- , keyword "rec" >> Rec <$> identifier <*> term
    ]

patternTerm :: Parser (Term Info)
patternTerm = pattern' >>= \p -> return (Pattern p)

operator :: Parser (Term Info -> Term Info -> Term Info)
operator =
  choice
    [ symbol "+"  >> return (\t1 t2 -> Plus  t1 t2 $ sourcePositions t1 t2)
    , symbol "-"  >> return (\t1 t2 -> Minus t1 t2 $ sourcePositions t1 t2)
    , symbol "<"  >> return (\t1 t2 -> Lt    t1 t2 $ sourcePositions t1 t2)
    , symbol ">"  >> return (\t1 t2 -> Gt    t1 t2 $ sourcePositions t1 t2)
    , symbol "==" >> return (\t1 t2 -> Equal t1 t2 $ sourcePositions t1 t2)
    , return $ \f x -> Application f x $ sourcePositions f x
    ]
  where
    sourcePositions t1 t2 = (fst (annotation t1), snd (annotation t2))

caseStatement :: Parser (Term Info)
caseStatement =
  do _ <- keyword "case"
     t <- term
     _ <- keyword "of"
     info $ Case t <$> many1 caseBranch

caseBranch :: Parser (Pattern Info, Term Info)
caseBranch =
  do _    <- symbol "|"
     alt  <- pattern'
     _    <- arrow
     body <- term
     return (alt, body)


desugaredIf :: Parser (Term Info)
desugaredIf =
  do _     <- keyword "if"
     t     <- term
     _     <- keyword "then"
     true  <- term
     _     <- keyword "else"
     false <- term
     b1    <- info $ return $ Boolean True
     b2    <- info $ return $ Boolean False
     info $ return $ Case t [(Value b1, true), (Value b2, false)]

termConstructor :: Parser (Term Info)
termConstructor = info $
  do ctr <- constructorName
     ts  <- option [] constructorList
     return $ TConstructor ctr ts

constructorList :: Parser [Term Info]
constructorList =
  do _  <- symbol "{"
     ts <- term `sepBy` symbol ","
     _  <- symbol "}"
     return ts


-- Functions, properties, signatures & data types
function :: Parser (Program Info -> Program Info)
function =
  do f    <- identifier
     args <- many $ info $ (,) <$> identifier
     _    <- symbol "="
     t    <- term
     let def = foldr (\(x, a) partial -> Lambda x partial a) t args
     return $ Function f def
  
property :: Parser (Program Info -> Program Info)
property =
  do p    <- identifier
     args <- many $ info $ (,) <$> identifier
     _    <- symbol "=*="
     t    <- term
     let def = foldr (\(x, a) partial -> Lambda x partial a) t args
     return $ Property p def
     
signature' :: Parser (Program Info -> Program Info)
signature' =
  do s <- identifier
     _ <- symbol "::"
     Signature s <$> type'


-- Algebraic Data Types
constructor :: Parser (C, [Type])
constructor =
  do c  <- constructorName
     ts <- many type'
     return (c, ts)

adt :: Parser (Program Info -> Program Info)
adt =
  do _  <- symbol "adt"
     t  <- constructorName
     _  <- symbol "="
     Data t <$> sepByPipe constructor


-- Program
program :: Parser (Program Info)
program = fmap (foldr id End) statements
  
statements :: Parser [Program Info -> Program Info]
statements =
  do prog <- many $
       choice
         [ try signature'
         , try adt
         , function
         , property
         ]
     _ <- eof
     return prog


-- Utility
info :: Parser (Info -> a) -> Parser a
info p =
  do start <- getPosition
     e     <- p
     end   <- getPosition
     return (e (start, end))

whitespace :: Parser ()
whitespace = void $ many $ void space <|> comment

lexeme :: Parser a -> Parser a
lexeme = (<* whitespace)

symbol :: String -> Parser ()
symbol = lexeme . void . try . string

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

dash :: Parser Char
dash = char '-'

underscore :: Parser Char
underscore = char '_'

arrow :: Parser ()
arrow = symbol "->"

reserved :: Name -> Bool
reserved = flip elem reservedKeywords

sepByPipe :: Parser a -> Parser [a]
sepByPipe p = p `sepBy1` symbol "|"
