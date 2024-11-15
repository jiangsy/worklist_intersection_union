import Test.Hspec

import Alg
import Parser

test :: FilePath -> Bool -> IO (Either String Bool)
test s mFlag = do
  code <- readFile s
  case parseExp code of
    Left err -> return $ Left err
    Right e -> return $ Right flag
      where
        b = pickNewTVar [] (tvarInExp e)
        ws = [WJug (Inf e b End)]
        (flag, _) = bigStep mFlag 0 400 "" ws

prettyPrint :: (String, Bool, Bool) -> String
prettyPrint (filename, flag, result) = filename ++ (if flag then ", MonoIU on" else "") ++ ", should be " ++ if result then "accepted" else "rejected"

main :: IO ()
main = do
  hspec $ do
    describe "Variant 1 examples" $ do
      testAll v1Map
    describe "Variant 2 examples" $ do
      testAll v2Map
  where testAll = mapM_ (\x@(filename, flag, result) -> it (prettyPrint x) (test ("examples/" ++ filename) flag >>= (`shouldBe` Right result)))

v1Map :: [(String, Bool, Bool)]
v1Map = 
  [ ("ex1_1.e", False, True)
  , ("ex1_2.e", False, True)
  , ("h1.e", False, True)
  , ("f2.e", False, True)
  , ("f3_1.e", False, True)
  , ("f3_2.e", False, True)
  , ("ex4_1.e", False, True)
  , ("ex4_2.e", False, True)
  , ("ex5_1.e", False, False)
  , ("ex5_2.e", False, True)
  , ("ex5_3.e", False, False)
  , ("ex5_4.e", False, True)
  , ("ex6.e", False, True)
  , ("ex7_1.e", False, True)
  , ("ex7_2.e", False, True)
  , ("ex8_1.e", False, True)
  , ("ex8_2.e", False, False)
  , ("ex8_3.e", False, True)
  , ("ex8_4.e", False, False)
  , ("h9.e", False, True)
  , ("ex9_1.e", False, True)
  , ("ex9_2.e", False, True)
  , ("ex10.e", False, True)
  , ("ex11.e", False, True)
  , ("ex12_1.e", False, True)
  , ("ex12_2.e", False, True)
  , ("ex13.e", False, True)
  , ("h14_1.e", False, False)
  , ("h14_2.e", False, False)
  , ("ex15.e", False, False)
  ]

v2Map :: [(String, Bool, Bool)]
v2Map = 
  [ ("ex1_1.e", True, True)
  , ("ex1_2.e", True, True)
  , ("h1.e", True, True)
  , ("f2.e", True, True)
  , ("f3_1.e", True, True)
  , ("f3_2.e", True, True)
  , ("ex4_1.e", True, True)
  , ("ex4_2.e", True, True)
  , ("ex5_1.e", True, False)
  , ("ex5_2.e", True, True)
  , ("ex5_3.e", True, False)
  , ("ex5_4.e", True, True)
  , ("ex6.e", True, True)
  , ("ex7_1.e", True, True)
  , ("ex7_2.e", True, True)
  , ("ex8_1.e", True, True)
  , ("ex8_2.e", True, False)
  , ("ex8_3.e", True, True)
  , ("ex8_4.e", True, True)
  , ("h9.e", True, True)
  , ("ex9_1.e", True, True)
  , ("ex9_2.e", True, True)
  , ("ex10.e", True, True)
  , ("ex11.e", True, True)
  , ("ex12_1.e", True, True)
  , ("ex12_2.e", True, True)
  , ("ex13.e", True, True)
  , ("h14_1.e", True, True)
  , ("h14_2.e", True, False)
  , ("ex15.e", True, False)
  ]
