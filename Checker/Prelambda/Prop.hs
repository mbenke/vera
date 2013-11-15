module Prelambda.Prop where
import Prelambda.Preterm
infixr 6 :->
infixl 9 :$

class ToP a where
      toP :: a -> Preterm

data Prop = TV Name | Prop :-> Prop
  deriving (Eq,Show)

instance Num Prop where
  fromInteger = TV . show
  abs = undefined
  signum = undefined
  (*) = undefined
  (+) = undefined

instance ToP Prop where
  toP (TV n) = Tvar n
  toP (p :-> q) = Tall "_" (toP p) (toP q)

data Proof = Var Name | Lam Name Proof | Proof :$ Proof 
  deriving(Eq,Show)

infixl 8 $$
($$) :: Proof -> [Proof] -> Proof
-- ($$) = foldl (:$) id
m $$ [] = m
m $$ (n:ns) = (m :$ n) $$ ns
