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
pattern' =
  (try $ parens $ pattern')
  <|>
  (choice $ map info
    [ number     <&> Number
    , boolean    <&> Boolean
    , Unit       <$ unit
    , identifier <&> Variable
    , try $ parens $ Pair <$> term <*> (char ',' *> term)
    ])


-- Complex Terms
term :: Parser (Term Info)
term = undefined


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
