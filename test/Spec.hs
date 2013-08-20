import Test.Hspec
import Control.Foldl as F
import qualified Data.Set as Set

main :: IO ()
main = hspec $ do
    describe "head" $ do
        it "works on total list" $
            fold F.head [1..10] `shouldBe` Just 1
        it "works on partial list" $
            fold F.head [1, undefined] `shouldBe` Just 1
        it "works on Set" $
            fold F.head (Set.fromList [1..10]) `shouldBe` Just 1
        it "works with foldM" $ do
            res <- foldM F.head [1..10]
            res `shouldBe` Just 1
        it "works with foldM+Set" $ do
            res <- foldM F.head $ Set.fromList [1..10]
            res `shouldBe` Just 1