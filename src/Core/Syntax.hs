{-# LANGUAGE DeriveFunctor #-}

{-------------------------------------------------------------------------------

  Module      : Core.Syntax
  Description : Abstract syntax of Contra.
  Copyright   : (c) 2024 Sophie Adeline Solheim Bosio
  License     : GLP-3.0

  Maintainer  : sophie.bosio@outlook.com
  Stability   : experimental
  Portability : POSIX

  The abstract syntax of the functional programming language Contra.

  This is a prototype version, first published as part of
  Sophie Bosio's MSc thesis at the University of Oslo, 2024.

  Besides the abstract syntax, this file also contains functions and
  typeclass instances pertaining to:
   - Term & program equality
   - Term canonicity (literals)
   - Term annotations
   - Pretty printing
   - Other utility functions

-------------------------------------------------------------------------------}

module Core.Syntax where

import Data.List (intercalate)


-- Abbreviations
type Index = Integer -- Unification variable index

type Name = String
type X    = Name     -- Variable name
type F    = Name     -- Function name
type P    = Name     -- Property name
type C    = Name     -- Data constructor name
type T    = Name     -- Data type name

type T0   a = Term    a
type T1   a = Term    a
type T2   a = Term    a
type P0   a = Pattern a

type Alt  a = Pattern a  -- Case alternative
type Body a = Term    a  -- Case alternative body


-- Abstract Syntax
data Program a =
    Signature X  Type         (Program a)  -- Type signature declaration
  | Data      T [Constructor] (Program a)  -- Algebraic data type declaration
  | Function  F (Term a)      (Program a)  -- Function declaration
  | Property  P (Term a)      (Program a)  -- Property declaration
  | End
  deriving (Functor)

data Type =
    Unit'
  | Integer'
  | Boolean'
  | Variable' Index
  | Type :->: Type
  | ADT  T
  | TypeList [Type] -- Only used internally

data Constructor = Constructor C [Type]

data Term a =
  -- Base terms:
    Pattern                     (Pattern a)
  | Lambda       (P0 a) (T0 a)            a
  | Application         (T1 a) (T2 a)     a
  | Let          (P0 a) (T1 a) (T2 a)     a
  | Case         (T0 a) [(Alt a, Body a)] a
  | TConstructor C      [Term a]          a
  -- | Rec         X      (T0 a)            a -- Future work
  -- Utilities:
  | Plus         (T0 a) (T1 a)            a
  | Minus        (T0 a) (T1 a)            a
  | Lt           (T0 a) (T1 a)            a
  | Gt           (T0 a) (T1 a)            a
  | Equal        (T0 a) (T1 a)            a
  | Not          (T0 a)                   a
  deriving (Functor)

data Pattern a =
    Value               (Value a)
  | Variable     X             a
  | List           [Pattern a] a
  | PConstructor C [Pattern a] a
  deriving (Functor)

data Value a =
    Unit                     a
  | Number       Integer     a
  | Boolean      Bool        a
  | VConstructor C [Value a] a
  deriving (Functor)


-- Canonical terms & Patterns
-- A canonical term is a pattern with no variables
class Canonical a where
  canonical :: a -> Bool

instance Canonical (Term a) where
  canonical (Pattern           p) = canonical p
  canonical (TConstructor _ ts _) = all canonical ts
  canonical _                     = False

instance Canonical (Pattern a) where
  canonical (Value             v) = canonical v
  canonical (Variable        _ _) = False
  canonical (List           ps _) = all canonical ps
  canonical (PConstructor _ ps _) = all canonical ps

instance Canonical (Value a) where
  canonical (Unit              _) = True
  canonical (Number          _ _) = True
  canonical (Boolean         _ _) = True
  canonical (VConstructor _ vs _) = all canonical vs


-- Working between terms, patterns, and values
strengthenToPattern :: Show a => Term a -> Pattern a
strengthenToPattern (TConstructor c ts a)
  | all isPattern ts = PConstructor c (map strengthenToPattern ts) a
strengthenToPattern (Pattern p) = p
strengthenToPattern t           = error $
  "Expected pattern, but was given the non-canonical term '" ++ show t ++ "'"

strengthenToValue :: Show a => Pattern a -> Value a
strengthenToValue (PConstructor c ps a)
  | all canonical ps = VConstructor c (map strengthenToValue ps) a
strengthenToValue (Value v) = v
strengthenToValue p         = error $
  "Expected value, but was given the non-canonical term '" ++ show p ++ "'"

weakenToPattern :: Value a -> Pattern a
weakenToPattern (VConstructor c vs a) = PConstructor c (map weakenToPattern vs) a
weakenToPattern v                     = Value v

weakenToTerm :: Pattern a -> Term a
weakenToTerm (PConstructor c ps a) = TConstructor c (map weakenToTerm ps) a
weakenToTerm p                     = Pattern p

manipulateWith :: Show a => (Term a -> Term a) -> (Pattern a -> Pattern a)
manipulateWith f = strengthenToPattern . f . weakenToTerm

isPattern :: Term a -> Bool
isPattern (Pattern _) = True
isPattern _           = False

strengthenIfPossible :: Show a => Name -> [Term a] -> a -> Term a
strengthenIfPossible c ts a =
  if all isPattern ts
     then let ps = map strengthenToPattern ts
          in  if all canonical ps
                 then let vs = map strengthenToValue ps
                      in  Pattern $ Value $ VConstructor c vs a
                 else Pattern $ PConstructor c ps a
     else TConstructor c ts a


-- Annotations
class Annotated term where
  annotation  :: term a -> a
  annotations :: term a -> [a]

instance Annotated Term where
  annotations (Pattern           p) = annotations p
  annotations (TConstructor _ ts a) = a : concatMap annotations ts
  annotations (Lambda _ t        a) = a : annotations t
  annotations (Let    _    t1 t2 a) = a : ([t1, t2]     >>= annotations)
  annotations (Application t1 t2 a) = a : ([t1, t2]     >>= annotations)
  annotations (Case     t0 ts    a) = a : annotations t0
                                      ++ concatMap (annotations . fst) ts
                                      ++ concatMap (annotations . snd) ts
  annotations (Plus     t0 t1    a) = a : ([t0, t1]     >>= annotations)
  annotations (Minus    t0 t1    a) = a : ([t0, t1]     >>= annotations)
  annotations (Lt       t0 t1    a) = a : ([t0, t1]     >>= annotations)
  annotations (Gt       t0 t1    a) = a : ([t0, t1]     >>= annotations)
  annotations (Equal    t0 t1    a) = a : ([t0, t1]     >>= annotations)
  annotations (Not      t0       a) = a : annotations t0
  annotation  t                     = head $ annotations t
  -- annotations (Rec    _ t0       a) = a : annotations t0 -- future work

instance Annotated Pattern where
  annotations (Value              v) = annotations v
  annotations (Variable        _  a) = return a
  annotations (List            ps a) = a : concatMap annotations ps
  annotations (PConstructor _  ps a) = a : concatMap annotations ps
  annotation  p                      = head $ annotations p

instance Annotated Value where
  annotations (Unit               a) = return a
  annotations (Number          _  a) = return a
  annotations (Boolean         _  a) = return a
  annotations (VConstructor _  vs a) = a : concatMap annotations vs
  annotation  v                      = head $ annotations v


-- Term Equality
instance Eq Type where
  (==) = equivalent

equivalent :: Type -> Type -> Bool
equivalent (Variable' _) _             = True
equivalent _            (Variable' _)  = True
equivalent Unit'        Unit'          = True
equivalent Integer'     Integer'       = True
equivalent Boolean'     Boolean'       = True
equivalent (t0 :->: t1) (t0' :->: t1') = t0 == t0' && t1 == t1'
equivalent (ADT      t) (ADT        s) = t == s
equivalent (TypeList   ts) (TypeList     ss) = and $ zipWith (==) ts ss 
equivalent _            _              = False

instance Eq Constructor where
  Constructor c [] == Constructor d [] = c == d
  Constructor c cs == Constructor d ds = c == d && and (zipWith (==) cs ds)

instance (Eq a) => Eq (Term a) where
  (Pattern      p) == (Pattern       q) = p == q
  (Plus   t0 t1 a) == (Plus  t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Minus  t0 t1 a) == (Minus t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Lt     t0 t1 a) == (Lt    t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Gt     t0 t1 a) == (Gt    t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Equal  t0 t1 a) == (Equal t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Not    t0    a) == (Not   t0'     b) = a == b && t0 == t0'
  (Lambda x  t  a) == (Lambda y  t'  b) = x == y &&  a == b   && t  == t'
  (Let  x t0 t1 a) == (Let y t0' t1' b) = x == y &&  a == b   &&
                                        t0 == t0' && t1 == t1'
  (Application t1 t2 a) == (Application t1' t2' b) =
    a == b && t1 == t1' && t2 == t2'
  (Case t0 cases a) == (Case t0' cases' b) =
    a  == b   &&
    t0 == t0' &&
    all (\((x, y), (x', y')) -> x == x' && y == y') (zip cases cases')
  (TConstructor c ts a) == (TConstructor d us b) = a == b &&
                                                   c == d &&
                                                   and (zipWith (==) ts us)
  _ == _ = False
  -- (Rec    x t0 a) == (Rec     y t0' b) = x == y &&  a == b   && t0 == t0'

instance (Eq a) => Eq (Pattern a) where
  (Value             v) == (Value             w) = v == w
  (Variable        x a) == (Variable        y b) = x == y && a == b
  (List           ps a) == (List           rs b) = a == b &&
                                                   and (zipWith (==) ps rs)
  (PConstructor c ps a) == (PConstructor d rs b) = a == b &&
                                                   c == d &&
                                                   and (zipWith (==) ps rs)
  _ == _ = False

instance (Eq a) => Eq (Value a) where
  (Unit              _) == (Unit                _) = True
  (Number       n    _) == (Number       m      _) = n == m
  (Boolean      b    _) == (Boolean      c      _) = b == c
  (VConstructor c vs a) == (VConstructor d ws   b) = a == b &&
                                                     c == d &&
                                                     and (zipWith (==) vs ws)
  _ == _ = False



-- Program Equality
instance (Eq a) => Eq (Program a) where
  End                   == End                    = True
  (Signature x t  rest) == (Signature y s  rest') =
    x == y &&
    t == s &&
    rest == rest'
  (Data      t cs rest) == (Data      s ds rest') =
    t  == s  &&
    cs == ds &&
    rest == rest'
  (Function  f t  rest) == (Function  g s  rest') =
    f == g &&
    t == s &&
    rest == rest'
  (Property  p t  rest) == (Property  q s  rest') =
    p == q &&
    t == s &&
    rest == rest'
  _ == _ = False


-- Utility functions
swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

instance Semigroup (Program a) where
  (Signature x t  p1) <> p2 = Signature x t  (p1 <> p2)
  (Function  f x  p1) <> p2 = Function  f x  (p1 <> p2)
  (Property  p xs p1) <> p2 = Property  p xs (p1 <> p2)
  (Data      t cs p1) <> p2 = Data      t cs (p1 <> p2)
  End                 <> p2 = p2

instance Monoid (Program a) where
  mempty  = End
  mappend = (<>)

signatures :: Program a -> [(F, Type)]
signatures (Signature x t rest) = (x, t) : signatures rest
signatures (Function  _ _ rest) = signatures rest
signatures (Property  _ _ rest) = signatures rest
signatures (Data      _ _ rest) = signatures rest
signatures _ = mempty

functions :: Program a -> [(F, Term a)]
functions (Signature _ _ rest) = functions rest
functions (Function  f x rest) = (f, x) : functions rest
functions (Property  _ _ rest) = functions rest
functions (Data _ _ rest) = functions rest
functions _                    = mempty

properties :: Program a -> [(P, Term a)]
properties (Signature _ _ rest) = properties rest
properties (Function  _ _ rest) = properties rest
properties (Property  p x rest) = (p, x) : properties rest
properties (Data      _ _ rest) = properties rest
properties _                    = mempty

datatypes :: Program a -> [(T, [Constructor])]
datatypes (Signature _ _ rest) = datatypes rest
datatypes (Function  _ _ rest) = datatypes rest
datatypes (Property  _ _ rest) = datatypes rest
datatypes (Data      x c rest) = (x, c) : datatypes rest
datatypes _                    = mempty

dataConstructors :: Program a -> [(Constructor, T)]
dataConstructors p = concatMap (fromConstructor . swap) (datatypes p)
  where
    fromConstructor :: ([Constructor], T) -> [(Constructor, T)]
    fromConstructor (ctrs, t) = [ (c, t) | c <- ctrs ]

constructorNames :: Program a -> [(C, T)]
constructorNames p = map (\(Constructor c _, t) -> (c, t)) (dataConstructors p)

constructorArgs :: Program a -> [(C, [Type])]
constructorArgs p = map (\(Constructor c ts) -> (c, ts)) constructors
  where
    constructors = map fst (dataConstructors p)


-- Pretty printing
parens :: String -> String
parens = ("(" ++) . (++ ")")

brackets :: String -> String
brackets = ("[" ++) . (++ "]")

caseArrow :: (Pattern a, Term a) -> String
caseArrow (p, t) = " | " ++ show p ++ " -> " ++ show t

instance Show a => Show (Program a) where
  show (Signature x t  rest) =
    x ++ " :: "  ++ show t  ++ "\n" ++ show rest
  show (Function  f t  rest) =
    f ++ " = "   ++ show t  ++ "\n\n" ++ show rest
  show (Property  p t  rest) =
    p ++ " =*= " ++ show t  ++ "\n\n" ++ show rest
  show (Data      t cs rest) =
    t ++ " = "   ++ show cs ++ "\n\n" ++ show rest
  show End                   = ""

instance Show Type where
  show Unit'         = "Unit"
  show Integer'      = "Integer"
  show Boolean'      = "Boolean"
  show (Variable' i) = "V" ++ show i
  show (t0  :->: t1) = show t0 ++ " -> " ++ show t1
  show (ADT       t) = t
  show (TypeList     ts) = "[" ++ intercalate ", " (map show ts) ++ "]"

instance Show Constructor where
  show (Constructor c []) = show c
  show (Constructor c cs) = show c ++ " (" ++ intercalate ", " (map show cs) ++ ")"

instance Show (Term a) where
  show (Pattern               p) = show p
  show (TConstructor c  ts    _) = c ++
    " {" ++ unwords (map show ts) ++ "}"
  show (Lambda       x  t     _) = parens $ "\\" ++ show x ++ " -> " ++ show t
  show (Let          x  t1 t2 _) = "let " ++ show x ++ " = " ++ show t1 ++
    " in " ++ show  t2
  show (Application     t1 t2 _) = show t1 ++ " " ++ parens (show t2)
  show (Case         t0 ts    _) = "case " ++ show t0 ++ " of" ++
    concatMap caseArrow ts
  show (Plus         t0 t1    _) = show t0 ++ " + "  ++ show t1
  show (Minus        t0 t1    _) = show t0 ++ " - "  ++ show t1
  show (Lt           t0 t1    _) = show t0 ++ " < "  ++ show t1
  show (Gt           t0 t1    _) = show t0 ++ " > "  ++ show t1
  show (Equal        t0 t1    _) = show t0 ++ " == " ++ show t1
  show (Not          t0       _) = "not " ++ parens (show t0)
  -- show (Rec          x  t0    _) = "rec " ++ x ++ " . " ++ show t0

instance Show (Pattern a) where
  show (Value             v) = show v
  show (Variable     x    _) = show x
  show (List           ps _) = "[" ++ intercalate ", " (map show ps) ++ "]"
  show (PConstructor c ps _) = c  ++
    " {" ++ unwords (map show ps) ++ "}"

instance Show (Value a) where
  show (Unit              _) = "()"
  show (Number       n    _) = show n
  show (Boolean      b    _) = show b
  show (VConstructor c vs _) = c ++
    " {" ++ unwords (map show vs) ++ "}"


-- "Direct" AST printing
-- This is mostly here to ask the parser to write the AST for us,
-- so that for testing, we can write normal programs instead of
-- writing ASTs by hand
programAST :: Program Type -> String
programAST (Signature x t rest) = "(Signature " ++ show x ++ " " ++ typeAST t
                                  ++ " " ++ programAST rest ++ ")"
programAST (Function  f t rest) = "(Function "  ++ show f ++ " " ++ termAST t
                                  ++ " " ++ programAST rest ++ ")"
programAST (Property  p t rest) = "(Property "  ++ show p ++ " " ++ termAST t
                                  ++ " " ++ programAST rest ++ ")"
programAST (Data     t cs rest) = "(Data " ++ show t
                                  ++ " [" ++ intercalate ", " (constructorASTs cs)
                                  ++ " " ++ programAST rest ++ ")"
programAST End = "End"

termAST :: Term Type -> String
termAST (Pattern              p) = "(Pattern " ++ patternAST p ++ ")"
termAST (Lambda         p t tau) = "(Lambda " ++ patternAST p
                                   ++ " " ++ termAST t
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Application  t1 t2 tau) = "(Application " ++ termAST t1
                                   ++ " " ++ termAST t2
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Let        p t1 t2 tau) = "(Let " ++ patternAST p
                                   ++ " " ++ termAST t1
                                   ++ " " ++ termAST t2
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Case          t cs tau) = "(Case " ++ termAST t ++ " ["
                                   ++ intercalate ", " (branchASTs cs) ++ "] "
                                   ++ typeAST tau ++ ")"
termAST (TConstructor  c ts tau) = "(TConstructor " ++ show c ++ " ["
                                   ++ intercalate ", " (map termAST ts)
                                   ++ "] " ++ typeAST tau ++ ")"
termAST (Plus         t0 t1 tau) = "(Plus " ++ termAST t0
                                   ++ " " ++ termAST t1
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Minus        t0 t1 tau) = "(Minus " ++ termAST t0
                                   ++ " " ++ termAST t1
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Lt           t0 t1 tau) = "(Lt " ++ termAST t0
                                   ++ " " ++ termAST t1
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Gt           t0 t1 tau) = "(Gt " ++ termAST t0
                                   ++ " " ++ termAST t1
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Equal        t0 t1 tau) = "(Equal " ++ termAST t0
                                   ++ " " ++ termAST t1
                                   ++ " " ++ typeAST tau ++ ")"
termAST (Not          t0    tau) = "(Not " ++ termAST t0
                                   ++ " " ++ typeAST tau ++ ")"

patternAST :: Pattern Type -> String
patternAST (Value               v) = "(Value " ++ valueAST v ++ ")"
patternAST (Variable        x tau) = "(Variable " ++ show x
                                     ++ " " ++ typeAST tau ++ ")"
patternAST (List           ps tau) = "(List ["
                                     ++ intercalate ", " (map patternAST ps)
                                     ++ "] " ++ typeAST tau ++ ")"
patternAST (PConstructor c ps tau) = "(PConstructor " ++ show c ++ " ["
                                     ++ intercalate ", " (map patternAST ps)
                                     ++ "] " ++ typeAST tau ++ ")"
                                     

valueAST :: Value Type -> String
valueAST (Unit              tau) = "(Unit " ++ typeAST tau ++ ")"
valueAST (Number       n    tau) = "(Number " ++ show n ++ " " ++ typeAST tau ++ ")"
valueAST (Boolean      b    tau) = "(Boolean " ++ show b ++ " " ++ typeAST tau ++ ")"
valueAST (VConstructor c vs tau) = "(VConstructor " ++ show c ++ " ["
                                     ++ intercalate ", " (map valueAST vs)
                                     ++ "] " ++ typeAST tau ++ ")"

branchASTs :: [(Pattern Type, Body Type)] -> [String]
branchASTs = foldr (\(p, b) s ->
                      ("(" ++ patternAST p ++ ", " ++ termAST b ++ ")") : s) []

constructorASTs :: [Constructor] -> [String]
constructorASTs = foldr (\(Constructor c ts) s ->
                           s ++ ["Constructor " ++ show c
                                  ++ " [" ++ types ts ++ "]"]) []
  where
    types ts = intercalate ", " (foldr (\t s -> s ++ [typeAST t]) [] ts)

typeAST :: Type -> String
typeAST Unit'         = "Unit'"
typeAST Integer'      = "Integer'"
typeAST Boolean'      = "Boolean'"
typeAST (Variable' i) = "(Variable' " ++ show i ++ ")"
typeAST (t0 :->:  t1) = "(" ++ typeAST t0 ++ " :->: " ++ typeAST t1 ++ ")"
typeAST (ADT       t) = "(ADT " ++ t ++ ")"
typeAST (TypeList    ts) = "(TypeList [" ++ intercalate ", " (map typeAST ts) ++ "])"
