-- a variant of Tiny with environment inverted
module TinyInv where
import Data.Map(Map)
import qualified Data.Map as Map
import Control.Monad(guard,mzero,mplus)

type Name = String
infixr 6 :->
infixl 9 :$

data Type = TV Name | Type :-> Type
  deriving (Eq,Ord,Show)

instance Num Type where
  fromInteger = TV . show
  abs = undefined
  signum = undefined
  (*) = undefined
  (+) = undefined

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

data Spine = Spine [Type] Name deriving Show

unwind :: Type -> Spine
unwind (TV n) = Spine [] n
unwind (t1:->t2) = Spine (t1:vs) tail where Spine vs tail = unwind t2

-- A candidate for type t is a term with Spine xs t
type Candidate = (Term,Spine)
type Env = Map Type [Candidate]

-- proof monad - to be extended later
type PM = [Term]

addHyp :: Term -> Type -> Env -> Env
addHyp h t env = Map.insertWith (++) (TV tail) [(h,spine)] env where 
  spine@(Spine _ tail) = unwind t
  
  
lookupP :: Type -> Env -> [Candidate]
lookupP = Map.findWithDefault [] 

prove :: Type -> [Term]
prove = pr [] Map.empty where
      pr :: [Name] -> Env -> Type -> [Term]
      pr hist env (t1 :-> t2) = do
         let h = hypName t1
         let env' = addHyp (Var h) t1 env
         p <- pr hist env' t2
         return $ Lam h p 
      pr hist env (TV a) = do
         guard $ notElem a hist
         (p,Spine v tail) <- lookupP (TV a) env
         guard $ tail == a 
         let hist' = a:hist
         as <- mapM (pr hist' env) v
         return $ p $$ as  