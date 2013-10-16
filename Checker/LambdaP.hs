module LambdaP where

type Name = String
data Kind = Kstar 
          | Kpi Name Type Kind
            
data Type = Tvar Name 
          | Tall Name Type Type 
          | Tapp Type Term
            
data Term = Mvar 
          | Mapp Term Term 
          | Mabs Name Type Term