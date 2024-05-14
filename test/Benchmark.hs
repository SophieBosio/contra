module Benchmark where

import Core.Syntax hiding (X)
import Validation.PropertyChecker

import qualified Test.Tasty.QuickCheck as QC
import Test.Tasty                  (TestTree, testGroup)
import Data.SBV
import Data.List                   (isPrefixOf, isInfixOf)
import Data.Char                   (isSpace)
import qualified Data.Map.Strict as Map


-- * Export
builtIn :: TestTree
builtIn =
  testGroup "Contra can find QuickCheck-generated counterexamples \
            \of built-in types: "
    [ QC.testProperty "QuickCheck-generated Booleans. " boolean
    , QC.testProperty "QuickCheck-generated Integers. " integer
    ]

mutuallyRecursive :: TestTree
mutuallyRecursive =
  testGroup "Contra can find QuickCheck-generated counterexamples \
            \of mutually recursive algebraic data types: "
    [ QC.testProperty "QuickCheck-generated A's. " a
    , QC.testProperty "QuickCheck-generated B's. " b
    , QC.testProperty "QuickCheck-generated X's. " x
    ]


-- * Built-in
boolean :: Bool -> QC.Property
boolean bool = QC.ioProperty $
  do let contraProgram = contraBoolean bool
     results <- checkTest contraProgram
     case concat results of
       [(_, value)] -> return $ bool == (read value :: Bool)
       _            -> return False

integer :: Int -> QC.Property
integer int = QC.ioProperty $
  do let v = toInteger int
     let contraProgram = contraInteger v
     results <- checkTest contraProgram
     case concat results of
       [(_, value)] -> return $ v == (read value :: Integer)
       _            -> return False

contraBoolean :: Bool -> Program Type
contraBoolean v =
  Signature "quickCheck" (Boolean' :->: Boolean')
   (Property "quickCheck"
    (Lambda (Variable "x" Boolean')
     (Case (Pattern (Variable "x" Boolean'))
      [(Value (Boolean v Boolean'), Pattern (Value (Boolean False Boolean')))
      ,(Variable "y" Boolean', Pattern (Value (Boolean True Boolean')))
      ]
      Boolean')
    (Boolean' :->: Boolean'))
    End)

contraInteger :: Integer -> Program Type
contraInteger v =
  Signature "quickCheck" (Integer' :->: Boolean')
   (Property "quickCheck"
    (Lambda (Variable "x" Integer')
     (Case (Pattern (Variable "x" Integer'))
      [(Value (Number v Integer'), Pattern (Value (Boolean False Boolean'))),
       (Variable "y" Integer', Pattern (Value (Boolean True Boolean')))
      ]
      Boolean')
     (Integer' :->: Boolean'))
    End)


-- * A and B
data A = Zero | One B deriving (Show, Eq)
data B = Null | Two A deriving (Show, Eq)

instance QC.Arbitrary A where
    arbitrary = QC.sized genA

genA :: Int -> QC.Gen A
genA 0 = QC.elements [Zero]
genA n = QC.oneof [return Zero, One <$> genB (n `div` 2)]

instance QC.Arbitrary B where
    arbitrary = QC.sized genB

genB :: Int -> QC.Gen B
genB 0 = QC.elements [Null]
genB n = QC.oneof [return Null, Two <$> genA (n `div` 2)]

a :: A -> QC.Property
a adt = QC.ioProperty $
  do let v = aToContra adt
     let contraProgram = contraA v
     results <- checkTest contraProgram
     case concat results of
       [(_, value)] -> return $ show v == value
       _            -> return False

b :: B -> QC.Property
b adt = QC.ioProperty $
  do let v = bToContra adt
     let contraProgram = contraB v
     results <- checkTest contraProgram
     case concat results of
       [(_, value)] -> return $ show v == value
       _            -> return False

contraA :: Value Type -> Program Type
contraA v =
  Data "A" [Constructor "Zero" [], Constructor "One" [ADT "B"]]
  (Data "B" [Constructor "Null" [], Constructor "Two" [ADT "A"]]
   (Signature "quickCheck" (ADT "A" :->: Boolean')
    (Property "quickCheck"
     (Lambda (Variable "x" (ADT "A"))
      (Case (Pattern (Variable "x" (ADT "A")))
       [(Value v, Pattern (Value (Boolean False Boolean')))
       ,(Variable "y" (ADT "A"), Pattern (Value (Boolean True Boolean')))]
       Boolean')
       (ADT "A" :->: Boolean'))
      End)))

contraB :: Value Type -> Program Type
contraB v =
  Data "A" [Constructor "Zero" [], Constructor "One" [ADT "B"]]
  (Data "B" [Constructor "Null" [], Constructor "Two" [ADT "A"]]
   (Signature "quickCheck" (ADT "B" :->: Boolean')
    (Property "quickCheck"
     (Lambda (Variable "x" (ADT "B"))
      (Case (Pattern (Variable "x" (ADT "B")))
       [(Value v, Pattern (Value (Boolean False Boolean')))
       ,(Variable "y" (ADT "B"), Pattern (Value (Boolean True Boolean')))]
       Boolean')
       (ADT "B" :->: Boolean'))
      End)))

aToContra :: A -> Value Type
aToContra Zero    = VConstructor "Zero" [] (ADT "A")
aToContra (One v) = VConstructor "One"  [bToContra v] (ADT "A")

bToContra :: B -> Value Type
bToContra Null    = VConstructor "Null" [] (ADT "B")
bToContra (Two v) = VConstructor "Two"  [aToContra v] (ADT "B")



-- * X Y Z W
data X = Stop | XY Y | XZ Z | XW W deriving (Show, Eq)
data Y = YY Bool Bool X            deriving (Show, Eq)
data Z = ZZ Bool      X            deriving (Show, Eq)
data W = WW Integer   X            deriving (Show, Eq)

instance QC.Arbitrary X where
    arbitrary = QC.sized genX

genX :: Int -> QC.Gen X
genX 0 = QC.elements [Stop]
genX n = QC.oneof
  [ return Stop
  , XY <$> genY (n `div` 3)
  , XZ <$> genZ (n `div` 3)
  , XW <$> genW (n `div` 3)
  ]

instance QC.Arbitrary Y where
    arbitrary = genY 0

genY :: Int -> QC.Gen Y
genY _ = YY <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary

instance QC.Arbitrary Z where
    arbitrary = genZ 0

genZ :: Int -> QC.Gen Z
genZ _ = ZZ <$> QC.arbitrary <*> QC.arbitrary

instance QC.Arbitrary W where
    arbitrary = genW 0

genW :: Int -> QC.Gen W
genW _ = WW <$> QC.arbitrary <*> QC.arbitrary


x :: X -> QC.Property
x adt = QC.ioProperty $
  do let v = xToContra adt
     let contraProgram = contraX v
     results <- checkTest contraProgram
     case concat results of
       [(_, value)] -> return $ show v == value
       _            -> return False

contraX :: Value Type -> Program Type
contraX v =
  Data "X" [Constructor "Stop" [],Constructor "XY" [ADT "Y"],Constructor "XZ" [ADT "Z"],Constructor "XW" [ADT "W"]]
  (Data "Y" [Constructor "YY" [Boolean',Boolean',ADT "X"]]
   (Data "Z" [Constructor "ZZ" [Boolean',ADT "X"]]
    (Data "W" [Constructor "WW" [Integer',ADT "X"]]
     (Signature "quickCheck" (ADT "X" :->: Boolean')
      (Property "quickCheck"
       (Lambda (Variable "x" (ADT "X"))
        (Case (Pattern (Variable "x" (ADT "X")))
         [(Value v, Pattern (Value (Boolean False Boolean')))
         ,(Variable "y" (ADT "X"), Pattern (Value (Boolean True Boolean')))
         ] Boolean')
         (ADT "X" :->: Boolean'))
        End)))))

xToContra :: X -> Value Type
xToContra Stop   = VConstructor "Stop" [] (ADT "X")
xToContra (XY y) = VConstructor "XY" [yToContra y] (ADT "X")
xToContra (XZ z) = VConstructor "XZ" [zToContra z] (ADT "X")
xToContra (XW w) = VConstructor "XW" [wToContra w] (ADT "X")

yToContra :: Y -> Value Type
yToContra (YY bool1 bool2 x') = VConstructor "YY" [Boolean bool1 Boolean', Boolean bool2 Boolean', xToContra x'] (ADT "Y")

zToContra :: Z -> Value Type
zToContra (ZZ bool x') = VConstructor "ZZ" [Boolean bool Boolean', xToContra x'] (ADT "Z")

wToContra :: W -> Value Type
wToContra (WW int x') = VConstructor "WW" [Number int Integer', xToContra x'] (ADT "W")


-- * Utility
checkTest :: Program Type -> IO [[(Name, String)]]
checkTest program =
   mapM (checkTestProperty program) (properties program)

checkTestProperty :: Program Type -> (P, Term Type) -> IO [(Name, String)]
checkTestProperty program prop =
  do let f = generateFormula 10 program (snd prop)
     let reconstructor = indexReconstruct program
     (ThmResult result) <- prove f
     case result of
       Unsatisfiable _ _ -> return []
       Satisfiable   _ _ -> return $ parseResults $
                            prettyPrint reconstructor $
                            Map.toList $ getModelDictionary result
       _                 -> return []


parseResults :: String -> [(Name, String)]
parseResults results = map (parseVal . splitAndTrim) $ removeInfo $ lines results
  where
    removeInfo [] = []
    removeInfo (l : rest) = if    "Checking"      `isPrefixOf` l
                               || "Counterexample" `isInfixOf` l
                            then removeInfo rest
                            else l : removeInfo rest
    parseVal (varName, cv) =
      let val = takeWhile (/= ':') cv in
        (varName, trim val)
    splitAndTrim result =
      let (varName, cv) = splitAtChar '=' result in
        (trim varName, trim cv)
    trim = f . f
    f = reverse . dropWhile isSpace
