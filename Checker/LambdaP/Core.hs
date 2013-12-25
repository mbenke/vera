module LambdaP.Core where

type Name = String
data Kind = Kstar 
          | Kpi Name Type Kind
            
data Type = Tvar Name 
          | Tall Name Type Type 
          | Tapp Type Term
          | Texi Name Type Type
          | Tand Type Type
          | Tor Type Type  
          | Tbot 
 
data Term = Mvar Name
          | Mapp Term Term 
          | Mlam Name Type Term
          | Mwit Type Term Term -- [m1,m2]_{∃ x:phi1.phi2}
          | Mabs Name Type Name Type Term Term
            -- abstract <x:phi1,y:phi2> = m1 in m2
          | Mtup Type Term Term
          | Mpi1 Term
          | Mpi2 Term
          | Min1 Type Term
          | Min2 Type Term
          | Mcas Term (Name,Type,Term) (Name,Type,Term)
          | Meps Type Term -- ex falso

