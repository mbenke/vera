{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
import Base.Church
import Data.Set(Set)
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map

type Query = (Env, Type)
type SEnv = [(Int, Type)]
type Tools = [(Term, Type)]

-- type History = Set Query

envToList :: Env -> [(Int, Type)]
envToList = IntMap.toList

envFromList :: [(Int,Type)] -> Env
envFromList = IntMap.fromList

toolsFromEnv :: Env -> Tools
toolsFromEnv env = [ (Var n, t) | (n,t) <- envToList env ]

trivial :: Query -> [Term]
trivial (env, goal) = [ m | (m,ty) <- toolsFromEnv env, ty == goal ]

-- The Ask class is useful, alas  GHC has problems finding right instances
-- hence queryT and queryP functions
class Ask t where
  query :: t -> Query

instance Ask Query where
  query = id

instance Ask Type where
  query t = (envFromList [], t)

instance Ask ([(Int, Type)], Type) where
  query (e, g) = (envFromList e, g)

queryT :: Type -> Query
queryT = query

queryP :: ([(Int, Type)], Type) -> Query
queryP = query

q0 = queryT (t 1) where t = TyCon

-- x1 : 1 |- ? : 1
q1 = queryP ([(1,t 1)],t 1) where t = TyCon

q2 = queryP ([(1,t 1),(2,t 2),(3,t 1)], t 1) where t = TyCon

