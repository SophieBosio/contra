module Benchmark where

import Core.Syntax hiding (X)
import Validation.PropertyChecker

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck


-- * Export
builtIn :: TestTree
builtIn =
  testGroup "Contra can find QuickCheck-generated counterexamples \
            \of built-in types: "
  basic

mutuallyRecursive :: TestTree
mutuallyRecursive =
  testGroup "Contra can find QuickCheck-generated counterexamples \
            \of mutually recursive algebraic data types: " $
       ab
    ++ xyzw


-- * Built-in
basic :: [TestTree]
basic = []


-- * A and B
data A = Zero | One B deriving (Show, Eq)
data B = Null | Two A deriving (Show, Eq)

instance Arbitrary A where
    arbitrary = sized genA

genA :: Int -> Gen A
genA 0 = elements [Zero]
genA n = oneof [return Zero, One <$> genB (n `div` 2)]

instance Arbitrary B where
    arbitrary = sized genB

genB :: Int -> Gen B
genB 0 = elements [Null]
genB n = oneof [return Null, Two <$> genA (n `div` 2)]

ab :: [TestTree]
ab = []


-- * X Y Z W
data X = Stop | XY Y | XZ Z | XW W deriving (Show, Eq)
data Y = YY ()      X              deriving (Show, Eq)
data Z = ZZ Bool    X              deriving (Show, Eq)
data W = WW Integer X              deriving (Show, Eq)

instance Arbitrary X where
    arbitrary = sized genX

genX :: Int -> Gen X
genX 0 = elements [Stop]
genX n = oneof [return Stop, XY <$> genY (n `div` 3), XZ <$> genZ (n `div` 3), XW <$> genW (n `div` 3)]

instance Arbitrary Y where
    arbitrary = genY 0

genY :: Int -> Gen Y
genY _ = YY () <$> arbitrary

instance Arbitrary Z where
    arbitrary = genZ 0

genZ :: Int -> Gen Z
genZ _ = ZZ <$> arbitrary <*> arbitrary

instance Arbitrary W where
    arbitrary = genW 0

genW :: Int -> Gen W
genW _ = WW <$> arbitrary <*> arbitrary


xyzw :: [TestTree]
xyzw = []
