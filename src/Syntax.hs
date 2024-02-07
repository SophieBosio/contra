{-# LANGUAGE DeriveFunctor #-}

module Syntax where


-- Abbreviations
type Index = Integer    -- Unification variable index

type Name = String
type X    = Name    -- Variable name
type F    = Name    -- Function name
type P    = Name    -- Property name
type C    = Name    -- Constructor name
type T    = Name    -- Type name

type T0   a = Term a
type T1   a = Term a
type T2   a = Term a

type Alt  a = Pattern a  -- Case alternative
type Body a = Term    a  -- Case alternative body


-- Abstract Syntax
data Program a =
    Signature X  Type         (Program a)  -- Type signature declaration
  | Data      T [(C, [Type])] (Program a)  -- Algebraic data type declaration
  | Function  F (Term a)      (Program a)  -- Function declaration
  | Property  P (Term a)      (Program a)  -- Property declaration
  | End
  deriving (Functor)

data Type =
    Unit'
  | Integer'
  | Boolean'
  | Variable' Index
  | Type :*:  Type
  | Type :->: Type
  | ADT  T    [Type]
  deriving (Show)

data Term a =
  -- Base terms:
    Pattern                     (Pattern a)
  | Lambda      X      (T0 a)            a
  | Rec         X      (T0 a)            a
  | Let         X      (T1 a) (T2 a)     a
  | Application (T1 a) (T2 a)            a
  | Case        (T0 a) [(Alt a, Body a)] a
  -- Utilities:
  | Plus        (T0 a) (T1 a)            a
  | Minus       (T0 a) (T1 a)            a 
  | Lt          (T0 a) (T1 a)            a
  | Gt          (T0 a) (T1 a)            a
  | Equal       (T0 a) (T1 a)            a
  | Not         (T0 a)                   a
  deriving (Functor)

data Pattern a =
    Variable    X             a
  | Constructor C [Pattern a] a
  | Unit                      a
  | Number      Integer       a
  | Boolean     Bool          a
  deriving (Functor)


-- Canonical terms
-- A canonical term is a pattern with no variables
class Canonical a where
  canonical :: a -> Bool

instance Canonical (Term a) where
  canonical (Pattern p) = canonical p
  canonical _           = False

instance Canonical (Pattern a) where
  canonical (Variable       _ _) = False
  canonical (Unit             _) = True
  canonical (Number         _ _) = True
  canonical (Boolean        _ _) = True
  canonical (Constructor _ ps _) = all canonical ps

strengthenToPattern :: Term a -> Pattern a
strengthenToPattern (Pattern p) = p
strengthenToPattern t           = error $
  "expected pattern, but was given the non-canonical term " ++ show t

weakenToTerm :: Pattern a -> Term a
weakenToTerm = Pattern

manipulateWith :: (Term a -> Term a) -> Pattern a -> Pattern a
manipulateWith f = strengthenToPattern . f . weakenToTerm


-- Pretty printing
parens :: String -> String
parens = ("(" ++) . (++ ")")

brackets :: String -> String
brackets = ("[" ++) . (++ "]")

caseArrow :: (Pattern a, Term a) -> String
caseArrow (p, t) = " ; " ++ show p ++ " -> " ++ show t

instance Show (Pattern a) where
  show (Variable    x        _) = show x
  show (Constructor c  ts    _) = c ++ concatMap show ts
  show (Unit       _) = "()"
  show (Number   n _) = show n
  show (Boolean     b        _) = show b

instance Show (Term a) where
  show (Pattern              p) = show p
  show (Lambda      x  t0    _) = parens $ "\\" ++ x ++ " -> " ++ show t0
  show (Rec         x  t0    _) = "rec " ++ x ++ " . " ++ show t0
  show (Let         x  t1 t2 _) = "let " ++ x ++ " = " ++ show t1 ++
    " in " ++ show t2
  show (Application    t1 t2 _) = show t1 ++ parens (show t2)
  show (Case        t0 ts    _) = "case " ++ show t0 ++ " of" ++
    concatMap caseArrow ts
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


-- Annotations
class Annotated term where
  annotation  :: term a -> a
  annotations :: term a -> [a]

instance Annotated Term where
  annotations (Pattern           p) = annotations p
  annotations (Lambda _ t0       a) = a : annotations t0
  annotations (Rec    _ t0       a) = a : annotations t0
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
  annotation  term                  = head $ annotations term

instance Annotated Pattern where
  annotations (Variable        _ a) = return a
  annotations (Constructor _ ts  a) = a : concatMap annotations ts
  annotations (Unit              a) = return a
  annotations (Number          _ a) = return a
  annotations (Boolean         _ a) = return a
  annotation  p                     = head $ annotations p


-- Term Equality
instance Eq Type where
  (==) = equivalent

equivalent :: Type -> Type -> Bool
equivalent (Variable' _) _   = True
equivalent _   (Variable' _) = True
equivalent Unit'    Unit'    = True
equivalent Integer' Integer' = True
equivalent Boolean' Boolean' = True
equivalent (t0 :*:  t1) (t0' :*:  t1') = t0 == t0' && t1 == t1'
equivalent (t0 :->: t1) (t0' :->: t1') = t0 == t0' && t1 == t1'
equivalent (ADT   t ts) (ADT    s ts') = t  == s   && and (zipWith (==) ts ts')
equivalent _ _ = False

instance (Eq a) => Eq (Term a) where
  (Pattern     p) == (Pattern       q) = p == q
  (Plus  t0 t1 a) == (Plus  t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Minus t0 t1 a) == (Minus t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Lt    t0 t1 a) == (Lt    t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Gt    t0 t1 a) == (Gt    t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Equal t0 t1 a) == (Equal t0' t1' b) = a == b && t0 == t0' && t1 == t1'
  (Not   t0    a) == (Not   t0'     b) = a == b && t0 == t0'
  (Lambda x t0 a) == (Lambda  y t0' b) = x == y &&  a == b   && t0 == t0'
  (Rec    x t0 a) == (Rec     y t0' b) = x == y &&  a == b   && t0 == t0'
  (Let x t0 t1 a) == (Let y t0' t1' b) = x == y   &&  a == b   &&
                                        t0 == t0' && t1 == t1'
  (Application t1 t2 a) == (Application t1' t2' b) =
    a == b && t1 == t1' && t2 == t2'
  (Case t0 cases a) == (Case t0' cases' b) =
    a  == b   &&
    t0 == t0' &&
    all (\((x, y), (x', y')) -> x == x' && y == y') (zip cases cases')
  _ == _ = False

instance (Eq a) => Eq (Pattern a) where
  (Variable    x     a) == (Variable    y       b) = x == y && a == b
  (Unit              _) == (Unit                _) = True
  (Number      n     _) == (Number      m       _) = n == m
  (Boolean     b     _) == (Boolean     c       _) = b == c
  (Constructor c  ps a) == (Constructor d   ps' b) = a  == b   &&
                                                     c  == d   &&
                                                     and (zipWith (==) ps ps')
  _ == _ = False


-- Utility functions
meta :: Term a -> a
meta (Pattern           p) = meta' p
meta (Lambda      _ _   a) = a
meta (Rec         _ _   a) = a
meta (Let         _ _ _ a) = a
meta (Application _ _   a) = a
meta (Case        _ _   a) = a
meta (Plus        _ _   a) = a
meta (Minus       _ _   a) = a
meta (Lt          _ _   a) = a
meta (Gt          _ _   a) = a
meta (Equal       _ _   a) = a
meta (Not         _     a) = a

meta' :: Pattern a -> a
meta' (Variable      _ a) = a
meta' (Unit            a) = a
meta' (Number        _ a) = a
meta' (Boolean       _ a) = a
meta' (Constructor _ _ a) = a

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

datatypes :: Program a -> [(T, [(C, [Type])])]
datatypes (Signature _ _ rest) = datatypes rest
datatypes (Function  _ _ rest) = datatypes rest
datatypes (Property  _ _ rest) = datatypes rest
datatypes (Data      x t rest) = (x, t) : datatypes rest
datatypes _                    = mempty

properties :: Program a -> [(P, Term a)]
properties (Signature _ _ rest) = properties rest
properties (Function  _ _ rest) = properties rest
properties (Property  p x rest) = (p, x) : properties rest
properties (Data      _ _ rest) = properties rest
properties _                    = mempty
