import Test.Tasty


timeoutSeconds :: Integer -> Timeout
timeoutSeconds = mkTimeout . (* 1000000)

main :: IO ()
main = defaultMain $ localOption (timeoutSeconds 10) tests

tests :: TestTree
tests =
  testGroup "Contra - Main Test Suite"
    [ 
    ]
