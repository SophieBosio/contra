module Benchmark where

import Core.Syntax hiding (X)
import Validation.PropertyChecker

import qualified Test.Tasty.QuickCheck as QC
import Test.Tasty                  (TestTree, testGroup)
import Data.SBV
import Data.List                   (lines, isPrefixOf, isInfixOf)
import Data.Char                   (isSpace)
import Control.Monad               (foldM)
import qualified Data.Map.Strict as Map


-- * Export
builtIn :: TestTree
builtIn =
  testGroup "Contra can find QuickCheck-generated counterexamples \
            \of built-in types: "
    [ QC.testProperty "Contra can find QuickCheck-generated Booleans. " boolean
    , QC.testProperty "Contra can find QuickCheck-generated Integers. " integer
    ]

mutuallyRecursive :: TestTree
mutuallyRecursive =
  testGroup "Contra can find QuickCheck-generated counterexamples \
            \of mutually recursive algebraic data types: " $
       ab
    ++ xyzw


-- * Built-in
boolean :: Bool -> QC.Property
boolean b = QC.ioProperty $
  do let contraProgram = contraBoolean b
     results <- checkTest contraProgram
     case concat results of
       [(_, value)] -> return $ b == (read value :: Bool)
       _            -> return False

integer :: Int -> QC.Property
integer i = QC.ioProperty $
  do let v = toInteger i
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

ab :: [TestTree]
ab = []


-- * X Y Z W
data X = Stop | XY Y | XZ Z | XW W deriving (Show, Eq)
data Y = YY ()      X              deriving (Show, Eq)
data Z = ZZ Bool    X              deriving (Show, Eq)
data W = WW Integer X              deriving (Show, Eq)

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
genY _ = YY () <$> QC.arbitrary

instance QC.Arbitrary Z where
    arbitrary = genZ 0

genZ :: Int -> QC.Gen Z
genZ _ = ZZ <$> QC.arbitrary <*> QC.arbitrary

instance QC.Arbitrary W where
    arbitrary = genW 0

genW :: Int -> QC.Gen W
genW _ = WW <$> QC.arbitrary <*> QC.arbitrary


xyzw :: [TestTree]
xyzw = []


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
    splitAtChar char str =
      let (before, after) = break (== char) str
      in  (before, drop 1 after)
