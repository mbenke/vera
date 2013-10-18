module LambdaP where

type Name = String
data Kind = Kstar 
          | Kpi Name Type Kind
            
data Type = Tvar Name 
          | Tall Name Type Type 
          | Tapp Type Term
            
data Term = Mvar Name
          | Mapp Term Term 
          | Mabs Name Type Term
            
dummy = "_"
karr = Kpi dummy 
tarr = Tall dummy

instance Num Type where
  fromInteger = Tvar . show
  (+) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  
k0 = Kstar
k1 = karr 0 k0
t1 = tarr 0 0
m1 = Mabs "x" 0 (Mvar "x")

instance Show Kind where            
  show Kstar = "*"
  show (Kpi n t k) = concat["(",n,":",show t,")->",show k]
  
instance Show Type where
  show (Tvar n) = n
  show (Tall n t1 t2) = concat ["(∀",n,":",show t1,")",show t2]
  show (Tapp t1 t2) = unwords [show t1,show t2]
  
instance Show Term where
  show (Mvar n) = n
  show (Mapp t1 t2) = unwords [show t1,show t2] 
  show (Mabs n t1 t2) = concat ["(","λ",n,":",show t1,".",show t2,")"]

  
