{-

  Module      : Core.Parser
  Description : The parser for Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  Parser for the functional language Contra.

  The language's concrete syntax closely resembles that
  of Haskell.

  The parser is implemented with the monadic parser
  combinator library Parsec.

  Besides strict parsing, the parser is responsible for "flattening" function
  definitions s.t. functions defined over different pattern-match cases are
  collapsed into a single function definition with a case statement representing
  the different pattern-matches defined.

  It also keeps track of the source position of each term so we can provide the
  user with more helpful type error messages.

-}

module Core.Parser where

import Core.Syntax hiding (parens)

import Text.Parsec
import Text.Parsec.Pos (newPos)
import Control.Monad   (void, when)
import Data.Functor    ((<&>))
import Data.List       (nub, (\\), groupBy, sortBy)


-- * Abbreviations
type Source = String
type Parser = Parsec Source ()
type Info   = (SourcePos, SourcePos)

data ParsingError =
    MultipleSignatures  X
  | MultipleADTs        X
  | MultipleCtrs        X
  | MultipleProperties (X, Info)
  | ParsingFailed      ParseError
  deriving Show


-- * Export
parseProgram :: Source -> IO (Either [ParsingError] (Program String))
parseProgram path =
  do src <- readFile path
     return $
       case runParser (whitespace >> program) () path src of
         (Left   err) -> Left $ return $ ParsingFailed err
         (Right code) ->
           case reportErrors code of
             [ ]  -> return $ prettySourcePositions $ flatten code
             errs -> Left errs

parseString :: Parser a -> String -> Either ParseError a
parseString p = runParser p () "<error>"
    

-- * Language basics
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
  ]

identHead :: Parser Char
identHead = lower <|> underscore

identTail :: Parser Char
identTail = try $ choice [ letter, digit, dash ]

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


-- * Types
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


-- * Values
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


-- * Patterns
pattern' :: Parser (Pattern Info)
pattern' = choice
  [ parens pattern'
  , Value <$> value
  , try patternConstructor
  , info $ identifier <&> Variable
  ]

-- * Terms
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


-- * Functions, properties, signatures & data types
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


-- * Algebraic Data Types
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


-- * Program
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


-- * Utility
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


-- * Flatten function definitions into a case statement with tuples
flatten :: Program a -> Program a
flatten p = update (newDefs defs) p
  where
    dups      = duplicates (functions p)
    defs      = collectDuplicates dups

duplicates :: [(F, Term a)] -> [(F, Term a)]
duplicates fs = filter (\(x, _) -> length (filter (== x) names) > 1) fs
  where names = map fst fs

collectDuplicates :: [(F, Term a)] -> [[(F, Term a)]]
collectDuplicates defs = groupBy (\(f, _) (g, _) -> f == g)
                         (sortBy (\(f, _) (g, _) -> compare f g) defs)

newDefs :: [[(F, Term a)]] -> [(F, Term a)]
newDefs [           ] = []
newDefs ([ ]  : rest) = newDefs rest
newDefs (defs : rest) =
  let fname = fst (head defs) in
  let terms = map snd defs
  in  (fname, rewriteDefs fname terms) : newDefs rest

update :: [(F, Term a)] -> (Program a -> Program a)
update defs p = foldl (flip findAndReplace) p defs

findAndReplace :: (F, Term a) -> (Program a -> Program a)
findAndReplace (f', t') (Function f t rest)
  | f == f'   = Function f' t' (removeDefinition (f', t') rest)
  | otherwise = Function f t (findAndReplace (f', t') rest)
findAndReplace (f', t') (Property p t rest)
  | p == f'   = Property f' t' (removeDefinition (f', t') rest)
  | otherwise = Property p t (findAndReplace (f', t') rest)
findAndReplace def (Signature x tau rest) =
  Signature x tau (findAndReplace def rest)
findAndReplace def (Data x ts rest) =
  Data      x ts  (findAndReplace def rest)
findAndReplace _ End = End

removeDefinition :: (F, Term a) -> (Program a -> Program a)
removeDefinition (f', t') (Function f t rest)
  | f == f'   = removeDefinition (f', t') rest
  | otherwise = Function f t (removeDefinition (f', t') rest)
removeDefinition (f', t') (Property  p t  rest)
  | p == f'   = removeDefinition (f', t') rest
  | otherwise = Property  p t  (removeDefinition (f', t') rest)
removeDefinition def (Signature x tau  rest) =
  Signature x tau (removeDefinition def rest)
removeDefinition def (Data      x ts rest) =
  Data      x ts  (removeDefinition def rest)
removeDefinition _ End = End

-- Combine the different definitions of the function
-- and rewrite them as a Case statement
rewriteDefs :: F -> [Term a] -> Term a
rewriteDefs fname defs =
  lambdas (Case (Pattern inputs) branches i) i
  where
    splits   = map splitLambda defs
    branches = map (\(alts, body) -> (List alts (annotation body), body)) splits
    inputs   = generateInputPatterns fname (map fst splits)
    lambdas  = generateLambdas inputs
    i        = annotation $ head defs

splitLambda :: Term a -> ([Pattern a], Term a)
splitLambda (Lambda p t@(Lambda{}) _) =
  let (alts, remaining) = splitLambda t
  in  (p : alts, remaining)
splitLambda (Lambda p t _) = ([p], t)
splitLambda t              = ([ ], t)

generateInputPatterns :: F -> [[Pattern a]] -> Pattern a
generateInputPatterns fname pps =
  if sameNoOfArguments pps
     then List (genVars ps) (annotation $ head ps)
     else error $ "Different number of arguments in function definitions for '"
          ++ show fname ++ "'"
  where
    ps = head pps

sameNoOfArguments :: [[Pattern a]] -> Bool
sameNoOfArguments (ps:pps) =
  all sameNo pps
  where
    sameNo qs = length ps == length qs
sameNoOfArguments _ = True

genVarNames :: [X]
genVarNames = concat $ concatMap (\x -> replicate x (generateName x)) [1..]
  where
    generateName :: Int -> [String]
    generateName x = map (replicate x) ['a'..'z']

genVars :: [Pattern a] -> [Pattern a]
genVars [] = []
genVars ps =
  let names = map ("*" ++) $ take (length ps) genVarNames in
  let i     = annotation (head ps)
  in  map (`Variable` i) names

generateLambdas :: Pattern a -> (Term a -> a -> Term a)
generateLambdas (List [p]     _) cases i2 =
  Lambda p cases i2
generateLambdas (List (p:ps) i1) cases i2 =
  Lambda p (generateLambdas (List ps i1) cases i2) i2
generateLambdas t cases i = Lambda t cases i


-- * Handling errors
reportErrors :: Program Info -> [ParsingError]
reportErrors p =
     [ MultipleSignatures  n         | n <- sigs  \\ nub sigs  ]
  ++ [ MultipleADTs        n         | n <- adts  \\ nub adts  ]
  ++ [ MultipleCtrs        n         | n <- ctrs  \\ nub ctrs  ]
  ++ [ MultipleProperties (n, pos n) | n <- props \\ nub props ]
  where
    sigs  = fst <$> signatures p
    adts  = fst <$> datatypes  p
    ctrs  = map (\(Constructor c _) -> c) $ concatMap snd $ datatypes p
    props = fst <$> properties p
    pos n =
      maybe
      (newPos "unknown parse error" 0 0, 
       newPos "unknown parse error" 0 0)
      annotation (lookup n (functions p ++ properties p))

report :: [ParsingError] -> String
report [] = ""
report ((MultipleSignatures n) : rest) =
  ("Multiple type signatures declared for function/property with name '"
   ++ n ++ "'\n")
  ++ report rest
report ((MultipleADTs n) : rest) =
  ("Multiple ADTs declared with name '" ++ n ++ "'\n")
  ++ report rest
report ((MultipleCtrs n) : rest) =
  ("Multiple constructors declared with name '" ++ n ++ "'\n")
  ++ report rest
report ((MultipleProperties (n, i) : rest)) =
  let (start, end) = i
  in ("Multiple properties declared with name '" ++ n ++
      "'\n beginning at \n" ++ show start ++ "\n and ending at\n"
      ++ show end ++ "\n")
     ++ report rest
report ((ParsingFailed err) : rest) =
  ("Parsing failed: " ++ show err ++ "\n")
  ++ report rest

prettyPrintInfo :: Info -> String
prettyPrintInfo (start, end) =
  "in file '" ++ sourceName start ++ "'\
  \ between " ++ showLineCol start ++ " and " ++ showLineCol end
  where
    showLineCol pos = "(line " ++ show (sourceLine pos) ++
                      ", column " ++ show (sourceColumn pos) ++ ")"

prettySourcePositions :: Program Info -> Program String
prettySourcePositions (Function  f t rest) =
  Function  f (pp t) $ prettySourcePositions rest
prettySourcePositions (Property  p t rest) =
  Property  p (pp t) $ prettySourcePositions rest
prettySourcePositions (Signature s t rest) =
  Signature s     t $ prettySourcePositions rest
prettySourcePositions (Data      d t rest) =
  Data      d     t  $ prettySourcePositions rest
prettySourcePositions End = End

pp :: Term Info -> Term String
pp (Pattern               p) = Pattern $ pp' p
pp (TConstructor c  ts    a) = TConstructor c (map pp ts)  (prettyPrintInfo a)
pp (Lambda       p  t     a) = Lambda      (pp' p) (pp t)  (prettyPrintInfo a)
pp (Let          p  t1 t2 a) = Let (pp' p) (pp t1) (pp t2) (prettyPrintInfo a)
pp (Application     t1 t2 a) = Application (pp t1) (pp t2) (prettyPrintInfo a)
pp (Case         t0 ts    a) = Case (pp t0)
                               (zip (map (pp' . fst) ts) (map (pp . snd) ts))
                               (prettyPrintInfo a)
pp (Plus         t0 t1    a) = Plus  (pp t0) (pp t1) (prettyPrintInfo a)
pp (Minus        t0 t1    a) = Minus (pp t0) (pp t1) (prettyPrintInfo a)
pp (Lt           t0 t1    a) = Lt    (pp t0) (pp t1) (prettyPrintInfo a)
pp (Gt           t0 t1    a) = Gt    (pp t0) (pp t1) (prettyPrintInfo a)
pp (Equal        t0 t1    a) = Equal (pp t0) (pp t1) (prettyPrintInfo a)
pp (Not          t0       a) = Not   (pp t0)         (prettyPrintInfo a)

pp' :: Pattern Info -> Pattern String
pp' (Value             v) = Value $ pp'' v
pp' (Variable     x    a) = Variable x (prettyPrintInfo a)
pp' (List           ps a) = List (map pp' ps) (prettyPrintInfo a)
pp' (PConstructor c ps a) = PConstructor c (map pp' ps) (prettyPrintInfo a)

pp'' :: Value Info -> Value String
pp'' (Unit              a) = Unit                         (prettyPrintInfo a)
pp'' (Number       n    a) = Number       n               (prettyPrintInfo a)
pp'' (Boolean      b    a) = Boolean      b               (prettyPrintInfo a)
pp'' (VConstructor c vs a) = VConstructor c (map pp'' vs) (prettyPrintInfo a)

