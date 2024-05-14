import Test.QuickCheck

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
