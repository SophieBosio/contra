{-# LANGUAGE DeriveFunctor #-}

module Syntax where


-- Abbreviations
type Index = Int    -- Unification variable index

type Name = String
type X    = Name    -- Variable name
type F    = Name    -- Function name
type P    = Name    -- Property name
type C    = Name    -- Constructor name
type T    = Name    -- Type name

type T0   a = Term a
type T1   a = Term a
type T2   a = Term a
type Alt  a = Term a  -- Case alternative
type Body a = Term a  -- Case alternative body


-- Abstract Syntax
data Program a =
    Signature X  Type         (Program a)  -- Type signature declaration
  | Function  F (Term a)      (Program a)  -- Function declaration
  | Property  P (Term a)      (Program a)  -- Property declaration
  | Data      T [(C, [Type])] (Program a)  -- Algebraic data type declaration
  | End
  deriving (Functor, Eq)

data Type =
    Unit'
  | Integer'
  | Boolean'
  | Variable' Index
  | Type :*:  Type
  | Type :->: Type
  | ADT  T    [Type]
  deriving (Eq, Show)

data Term a =
  -- Base terms:
    Pattern (Pattern a)
  | Lambda      X      (T0 a)            a
  | Application (T1 a) (T2 a)            a
  | If          (T0 a) (T1 a) (T2 a)     a
  | Case        (T0 a) [(Alt a, Body a)] a
  -- Utilities:
  | Fst         (T0 a)                   a
  | Snd         (T0 a)                   a
  | Plus        (T0 a) (T1 a)            a
  | Minus       (T0 a) (T1 a)            a 
  | Lt          (T0 a) (T1 a)            a
  | Gt          (T0 a) (T1 a)            a
  | Equal       (T0 a) (T1 a)            a
  | Not         (T0 a)                   a
  deriving (Functor, Eq)

data Pattern a =
    Variable X a
  | Constructor C [Pattern a] a
  | Unit a
  | Number Integer a
  | Boolean Bool a
  | Pair (T0 a) (T1 a) a
  deriving (Functor, Eq)


-- Canonical terms
-- A canonical term is a pattern with no variables


-- Pretty printing
parens :: String -> String
parens = ("(" ++) . (++ ")")

brackets :: String -> String
brackets = ("[" ++) . (++ "]")

caseArrow :: (Term a, Term a) -> String
caseArrow (t1, t2) = " ; " ++ show t1 ++ " -> " ++ show t2

instance Show (Pattern a) where
  show (Variable    x        _) = show x
  show (Constructor c  ts    _) = c ++ concatMap show ts
  show (Unit       _) = "()"
  show (Number   n _) = show n
  show (Boolean     b        _) = show b
  show (Pair           t1 t2 _) = parens $ show t1 ++ ", " ++ show t2

instance Show (Term a) where
  show (Pattern              p) = show p
  show (Lambda      x  t0    _) = parens $ "\\" ++ x ++ " -> " ++ show t0
  show (Application    t1 t2 _) = show t1 ++ parens (show t2)
  show (If          t0 t1 t2 _) = "if " ++ show t0 ++ " then " ++
    show t1 ++ " else " ++ show t2
  show (Case        t0 ts    _) = "case " ++ show t0 ++ " of" ++
    concatMap caseArrow ts
  show (Fst         t0       _) = "fst " ++ show t0
  show (Snd         t0       _) = "snd " ++ show t0
  show (Plus        t0 t1    _) = show t0 ++ " + "  ++ show t1
  show (Minus       t0 t1    _) = show t0 ++ " - "  ++ show t1
  show (Lt          t0 t1    _) = show t0 ++ " < "  ++ show t1
  show (Gt          t0 t1    _) = show t0 ++ " > "  ++ show t1
  show (Equal       t0 t1    _) = show t0 ++ " == " ++ show t1
  show (Not         t0       _) = "not" ++ parens (show t0)

instance Show a => Show (Program a) where
  show (Signature x t  rest) =
    x ++ " :: "  ++ show t  ++ "\n\n" ++ show rest
  show (Function  f t  rest) =
    f ++ " = "   ++ show t  ++ "\n\n" ++ show rest
  show (Property  p t  rest) =
    p ++ " =*= " ++ show t  ++ "\n\n" ++ show rest
  show (Data      t cs rest) =
    -- /!\ Might have to destructure pair first
    t ++ " = "   ++ show cs ++ concatMap show cs ++ "\n\n" ++ show rest
  show End                   = ""
