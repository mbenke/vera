module Tiny where
import Data.Map(Map)
import qualified Data.Map as Map
import Control.Monad(guard)

type Name = String
infixr 6 :->
infixl 9 :$

data Type = TV Name | Type :-> Type
  deriving (Eq,Show)

instance Num Type where
  fromInteger = TV . show
  abs = undefined
  signum = undefined
  (*) = undefined
  (+) = undefined
  (-) = undefined

hypName :: Type -> Name
hypName = ('h':).mangleTy
mangleTy (TV n) = n
mangleTy (t :-> u) = concat["L",mangleTy t,"D",mangleTy u,"I"]

data Term = Var Name | Lam Name Term | Term :$ Term 
  deriving(Eq,Show)

infixl 8 $$
($$) :: Term -> [Term] -> Term
-- ($$) = foldl (:$) id
m $$ [] = m
m $$ (n:ns) = (m :$ n) $$ ns

type Env = Map Name Type

data Spine = Spine [Type] Name deriving Show

unwind :: Type -> Spine
unwind (TV n) = Spine [] n
unwind (t1:->t2) = Spine (t1:vs) tail where Spine vs tail = unwind t2

prove :: Type -> [Term]
prove = pr [] Map.empty where
      pr :: [Name] -> Env -> Type -> [Term]
      pr hist env (t1 :-> t2) = do
         let h = hypName t1
         let env' = Map.insert h t1 env
         p <- pr hist env' t2
         return $ Lam h p 
      pr hist env (TV a) = do
         guard $ notElem a hist
         (x,t) <- Map.toList env
         let Spine v tail = unwind t
         guard $ tail == a 
         let hist' = a:hist
         as <- mapM (pr hist' env) v
         return (Var x $$ as)

 
-- | Tests
--
-- >>> prove $ 0 :-> 0
-- [Lam "h0" (Var "h0")]
--
-- >>> prove $ (0 :-> 1):-> (1:->0) :-> 1
-- []

-- FIXME
test3 = prove $ (0 :-> 1):-> (1:->0) :-> 0 :-> 1
