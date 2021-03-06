module Base.ChurchSpec(main, spec) where

import Test.Hspec
import Base.Church

-- `main` is here so that this module can be run from GHCi on its own.  It is
-- not needed for automatic spec discovery.
main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "typeOf" $ do
    it "typechecks I" $ do
      typeOf emptyEnv tmI `shouldBe` tyI
    it "typechecks K" $ do
      typeOf emptyEnv tmK `shouldBe` tyK
    it "typechecks S" $ do
      typeOf emptyEnv tmS `shouldBe` tyS

