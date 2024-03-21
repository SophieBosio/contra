module Core.Parser where

import Core.Syntax hiding (parens)

import Text.Parsec
import Text.Parsec.Pos (newPos)
import Control.Monad (void, when)
import Data.Functor ((<&>))
import Data.List (nub, (\\), groupBy, sortBy)


-- Abbreviations
type Source = String
type Parser = Parsec Source ()
type Info   = (SourcePos, SourcePos)

data ParsingError =
    MultipleSignatures           X
  | MultipleADTs                 X
  | MultipleProperties          (X, Info)
  | DifferentNumbersOfArguments (X, Info)
  | ParsingFailed               ParseError
  deriving Show


-- Export
parseProgram :: Source -> IO (Either [ParsingError] (Program Info))
parseProgram path =
  do src <- readFile path
     return $
       case runParser (whitespace >> program) () path src of
         (Left   err) -> Left $ return $ ParsingFailed err
         (Right code) ->
           case reportErrors code of
             [ ]  -> return code
             errs -> Left errs

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
  ++ [ try valueConstructor ]


-- Patterns
pattern' :: Parser (Pattern Info)
pattern' = choice
  [ parens pattern'
  , Value <$> value
  , try patternConstructor
  , info $ identifier <&> Variable
  ]

-- Terms
term :: Parser (Term Info)
term = choice $
  chainl1 simpleTerm operator :
  map try
    [ caseStatement
    , desugaredIf
    , termConstructor
    ]
  ++
  map info
    [ symbol  "\\"  >> Lambda <$> pattern' <*> (arrow >> term)
    , keyword "not" >> Not    <$> term
    , keyword "let" >> Let    <$> pattern' <*>
                       (symbol "=" >> term)  <*> (symbol "in" >> term)
    -- , keyword "rec" >> Rec <$> identifier <*> term
    ]

simpleTerm :: Parser (Term Info)
simpleTerm =
  choice
    [ -- Parentheses around any term, to explicate right-associative operations
      parens term
      -- Pattern interpreted as a term
    , pattern' >>= \p -> return (Pattern p)
    ]

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
  do _    <- symbol ";"
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
     ts  <- option [] (constructorList term)
     return $ TConstructor ctr ts

patternConstructor :: Parser (Pattern Info)
patternConstructor = info $
  do ctr <- constructorName
     ps  <- option [] (constructorList pattern')
     return $ PConstructor ctr ps

valueConstructor :: Parser (Value Info)
valueConstructor = info $
  do ctr <- constructorName
     vs  <- option [] (constructorList value)
     return $ VConstructor ctr vs

constructorList :: Parser a -> Parser [a]
constructorList p =
  do _  <- symbol "{"
     ts <- p `sepBy` symbol ","
     _  <- symbol "}"
     return ts


-- Functions, properties, signatures & data types
function :: Parser (Program Info -> Program Info)
function =
  do f    <- identifier
     args <- many $ info $ (,) <$> pattern'
     _    <- symbol "="
     t    <- term
     _    <- symbol "."
     let def = foldr (\(x, a) partial -> Lambda x partial a) t args
     return $ Function f def
  
property :: Parser (Program Info -> Program Info)
property =
  do p    <- identifier
     args <- many $ info $ (,) <$> pattern'
     _    <- symbol "=*="
     t    <- term
     _    <- symbol "."
     let def = foldr (\(x, a) partial -> Lambda x partial a) t args
     return $ Property p def
     
signature' :: Parser (Program Info -> Program Info)
signature' =
  do s <- identifier
     _ <- symbol "::"
     t <- type'
     _ <- symbol "."
     return $ Signature s t


-- Algebraic Data Types
constructor :: Parser Constructor
constructor =
  do c  <- constructorName
     ts <- many type'
     return $ Constructor c ts

adt :: Parser (Program Info -> Program Info)
adt =
  do _  <- symbol "adt"
     t  <- constructorName
     _  <- symbol "="
     cs <- constructor `sepBy1` symbol "|"
     _  <- symbol "."
     return $ Data t cs


-- Program
program :: Parser (Program Info)
program = whitespace >> fmap (foldr id End) statements
  
statements :: Parser [Program Info -> Program Info]
statements =
  do prog <- many $
       choice
         [ try signature'
         , try adt
         , try property
         , try function
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

dash :: Parser Char
dash = char '-'

underscore :: Parser Char
underscore = char '_'

arrow :: Parser ()
arrow = symbol "->"

reserved :: Name -> Bool
reserved = flip elem reservedKeywords


-- Flatten function definitions into a case statement with tuples
flatten :: Program Info -> Program Info
flatten p = newDefs defs <> remaining
  where
    dups      = duplicates (functions p)
    defs      = collectDuplicates dups
    remaining = foldr removeDefinition p dups
    updated   = foldr updateSig remaining dups

duplicates :: [(F, Term a)] -> [(F, Term a)]
duplicates fs = filter (\(x, _) -> length (filter (== x) names) > 1) fs
  where names = map fst fs

collectDuplicates :: [(F, Term a)] -> [[(F, Term a)]]
collectDuplicates defs = groupBy (\(f, _) (g, _) -> f == g)
                         (sortBy (\(f, _) (g, _) -> compare f g) defs)

newDefs :: [[(F, Term Info)]] -> Program Info
newDefs [           ] = End
newDefs ([ ]  : rest) = newDefs rest
newDefs (defs : rest) =
  let fname = fst (head defs) in
  let terms = map snd defs
  in  Function fname (rewriteDefs terms) $ newDefs rest

-- Combine the different definitions of the function
-- and rewrite them as a Case statement
rewriteDefs :: [Term Info] -> Term Info
rewriteDefs defs =
  Lambda (Variable "*x" info1)
    (Case (Pattern (Variable "*x" info1)) branches info2) info2
  where
    branches = foldr (\def cases -> cases ++ [tuples def]) [] defs
    info1    = annotation $ head defs
    info2    = annotation $ last defs

tuples :: Term Info -> (Pattern Info, Term Info)
tuples (Lambda p t@(Lambda{}) i) =
  let (args, remaining) = tuples t
  in  (Pair p args i, remaining)
tuples (Lambda p t i) = (p, t)

removeDefinition :: (F, Term a) -> Program a -> Program a
removeDefinition (f', t') (Function f t rest)
  | f == f'   = removeDefinition (f', t') rest
  | otherwise = Function f t (removeDefinition (f', t') rest)
removeDefinition def (Property  x t  rest) =
  Property  x t  (removeDefinition def rest)
removeDefinition def (Signature x t  rest) =
  Signature x t  (removeDefinition def rest)
removeDefinition def (Data      x ts rest) =
  Data      x ts (removeDefinition def rest)
removeDefinition _ End = End

updateSig = undefined


-- Handling errors
reportErrors :: Program Info -> [ParsingError]
reportErrors p =
     [ MultipleSignatures  n         | n <- sigs  \\ nub sigs  ]
  ++ [ MultipleADTs        n         | n <- adts  \\ nub adts  ]
  ++ [ MultipleProperties (n, pos n) | n <- props \\ nub props ]
  where
    sigs  = fst <$> signatures p
    adts  = fst <$> datatypes  p
    props = fst <$> properties p
    pos n =
      maybe
      (newPos "unknown parse error" 0 0, 
       newPos "unknown parse error" 0 0)
      annotation (lookup n (functions p ++ properties p))

report :: [ParsingError] -> String
report [] = ""
report ((MultipleSignatures n) : rest) =
  ("Multiple type signatures declared for function/property with name '" ++ n ++ "'\n")
  ++ report rest
report ((MultipleADTs n) : rest) =
  ("Multiple ADTs declared with name '" ++ n ++ "'\n")
  ++ report rest
report ((MultipleProperties (n, i) : rest)) =
  let (start, end) = i
  in ("Multiple properties declared with name '" ++ n ++
      "'\n beginning at \n" ++ show start ++ "\n and ending at\n" ++ show end ++ "\n")
     ++ report rest
report ((DifferentNumbersOfArguments (n, i)) : rest) =
  let (start, end) = i
  in  ("Function definitions for '" ++ n ++ "' have different numbers of arguments."
       ++ "\n beginning at \n" ++ show start ++ "\n and ending at\n" ++ show end ++ "\n")
      ++ report rest
report ((ParsingFailed err) : rest) =
  ("Parsing failed: " ++ show err ++ "\n")
  ++ report rest

