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

data Error =
    ReservedKeyword      (X, Info)
  | MultipleSignatures    X
  | MultipleADTs          X
  | MultipleFunctions    (X, Info)
  | MultipleProperties   (X, Info)
  | ParsingFailed        ParseError
  deriving Show

-- TODO: Deal with errors
reportErrors :: Program Info -> [Error]
reportErrors program =
     [ MultipleSignatures  n         | n <- sigs  \\ nub sigs  ]
  ++ [ MultipleADTs        n         | n <- adts  \\ nub adts  ]
  ++ [ MultipleFunctions  (n, pos n) | n <- funcs \\ nub funcs ]
  ++ [ MultipleProperties (n, pos n) | n <- props \\ nub props ]
  where
    sigs  = fst <$> signatures program
    adts  = fst <$> datatypes  program
    funcs = fst <$> functions  program
    props = fst <$> properties program
    pos n =
      maybe
      (newPos "unknown parse error" 0 0, 
       newPos "unknown parse error" 0 0)
      meta (lookup n (functions program ++ properties program))


-- Export
parseProgram :: Source -> IO (Either [Error] (Program Info))
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
parseString p = runParser p () "<repl>"
    

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
  , "adt"
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

constructorName :: Parser String
constructorName =
  do name <- (:) <$> upper <*> many identTail
     lexeme $ return name

keyword :: String -> Parser ()
keyword s = lexeme $ try $ string s >> notFollowedBy identTail


-- Types
type' :: Parser Type
type' = choice
  [ try $ partialArrowType type'
  , regularType
  ]

regularType :: Parser Type
regularType = choice
  [ try $ parens $ partialProductType type'
  , simpleType
  ]

simpleType :: Parser Type
simpleType = choice
  [ Unit'     <$  unit
  , Integer'  <$  symbol "Integer"
  , Boolean'  <$  symbol "Boolean"
  , Variable' <$> number
  , ADT       <$> identifier <*> many type'
  , parens type'
  ]

partialArrowType :: Parser Type -> Parser Type
partialArrowType retType =
  do argType <- regularType
     arrow >> (argType :->:) <$> retType

partialProductType :: Parser Type -> Parser Type
partialProductType t2 =
  do t1 <- type'
     symbol "," >> (t1 :*:) <$> t2


-- Patterns
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

pattern' :: Parser (Pattern Info)
pattern' = choice $
  try (parens pattern') :
  map info
    [ number      <&> Number
    , boolean     <&> Boolean
    , Unit        <$  unit
    , identifier  <&> Variable
    , Constructor <$> constructorName <*> many pattern'
    , try $ parens $ Pair <$> term <*> (char ',' *> term)
    ]


-- Complex terms
term :: Parser (Term Info)
term = choice $
  map try $
  [ caseStatement
  , desugaredIf
  , binaryOperator term
  , application term
  ]
  ++
  map info
    [ keyword "not" >> (Not <$> term)
    , keyword "fst" >> (Fst <$> term)
    , keyword "snd" >> (Snd <$> term)
    , keyword "\\"  >> Lambda <$> identifier <*> (arrow >> term)
    , keyword "rec" >> Rec <$> identifier <*> term
    , symbol  "let" >> Let <$> identifier <*>
                      (symbol "=" >> term) <*> (symbol "in" >> term)
    ]
  ++
  [ Pattern <$> pattern'
  , parens term
  ]

caseStatement :: Parser (Term Info)
caseStatement =
  do _ <- keyword "case"
     t <- term
     _ <- keyword "of"
     info $ Case t <$> many1
       (do _    <- symbol "|"
           alt  <- pattern'
           _    <- arrow
           body <- term
           return (alt, body))

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
     info $ return $ Case t [(b1, true), (b2, false)]

binaryOperator :: Parser (Term Info) -> Parser (Term Info)
binaryOperator t2 =
  do t1 <- term
     operator <- choice
       [ symbol "+"   >> return Plus
       , symbol "-"   >> return Minus
       , symbol "<"   >> return Lt
       , symbol ">"   >> return Gt
       , symbol "=="  >> return Equal
       ]
     info $ operator t1 <$> t2

application :: Parser (Term Info) -> Parser (Term Info)
application t2 =
  do t1 <- term
     info $ Application t1 <$> t2


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

constructors :: Parser [(C, [Type])]
constructors = constructor `sepBy1` symbol "|"

adt :: Parser (Program Info -> Program Info)
adt =
  do _  <- symbol "adt"
     t  <- constructorName
     _  <- symbol "="
     Data t <$> constructors


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