module XYZW where

import Test.Tasty.QuickCheck

data X = Stop | XY Y | XZ Z | XW W deriving (Show, Eq)
data Y = YY ()      X              deriving (Show, Eq)
data Z = ZZ Bool    X              deriving (Show, Eq)
data W = WW Integer X              deriving (Show, Eq)

instance Arbitrary X where
    arbitrary = sized genX

genX :: Int -> Gen X
genX 0 = elements [Stop]
genX n = oneof
  [ return Stop
  , XY <$> genY (n `div` 3)
  , XZ <$> genZ (n `div` 3)
  , XW <$> genW (n `div` 3)
  ]

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
