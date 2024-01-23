module Parser where

import Syntax hiding (parens)

import Text.Parsec
import Control.Monad (void, when)
import Data.Functor ((<&>))


-- Abbreviations
type Source = String
type Parser = Parsec Source ()
type Info   = (SourcePos, SourcePos)

data ParseError =
    ReservedKeyword      X Info
  | MultipleDeclarations X Info
  | MultipleDefinitions  X Info


-- Export
-- parseProgram :: Source -> IO (Either [Error] (Program Info))
-- parseProgram path =
--   do src <- readFile path
     

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
  , "fst"
  , "snd"
  , "let"
  , "in"
  , "rec"
  ]

identHead :: Parser Char
identHead = letter <|> underscore

identTail :: Parser Char
identTail = try $ choice [ identHead, digit, dash, underscore ]

identifier :: Parser String
identifier =
  do name <- (:) <$> identHead <*> many identTail
     when (reserved name) $ fail $ "reserved keyword " ++ name
     lexeme $ return name

keyword :: String -> Parser ()
keyword s = lexeme $ try $ string s >> notFollowedBy identTail


-- Types
type' :: Parser Type
type' = choice
  [ partialArrowType type'
  , simpleType
  ]

regularType :: Parser Type
regularType = choice
  [ partialProductType simpleType
  , simpleType
  ]

simpleType :: Parser Type
simpleType = choice
  [ Unit'     <$  unit
  , Integer'  <$  symbol "Integer"
  , Boolean'  <$  symbol "Boolean"
  , Variable' <$> number
  -- TODO! ADT
  , parens type'
  ]

partialArrowType :: Parser Type -> Parser Type
partialArrowType retType =
  do argType <- try regularType
     symbol "->" >> (argType :->:) <$> retType

partialProductType :: Parser Type -> Parser Type
partialProductType t2 =
  do t1 <- try $ parens simpleType
     symbol "," >> (t1 :*:) <$> t2


-- Patterns
number :: Parser Integer
number = lexeme $ fmap read $ (++) <$> prefix <*> digits
  where prefix = option "" $ string "-"
        digits = string "0" <|> many1 digit

boolean :: Parser Bool
boolean = choice
  [ symbol "True"  >> return True
  , symbol "False" >> return False
  ]

unit :: Parser ()
unit = void $ symbol "()"

pattern' :: Parser (Pattern Info)
pattern' = choice $
  try (parens pattern') :
  map info
    [ number     <&> Number
    , boolean    <&> Boolean
    , Unit       <$ unit
    , identifier <&> Variable
    -- TODO Constructor!
    , try $ parens $ Pair <$> term <*> (char ',' *> term)
    ]


-- Complex Terms
term :: Parser (Term Info)
term = undefined


-- Functions & Properties
func :: Parser ()
func = undefined

prop :: Parser ()
prop = undefined


-- Program
program :: Parser (Program Info)
program = undefined


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

reserved :: Name -> Bool
reserved = flip elem reservedKeywords
