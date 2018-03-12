module Base.IntChurch(
  Term(..), ($$), lam, Type(..),
  tmI, tmK, tmS,
  tyI, tyK, tyS,
  Env, emptyEnv, typeOf
                  ) where
-- Borrowing some ideas from Augustsson's "Lambda Calculus Cooked 4 ways"
-- http://www.augustsson.net/Darcs/Lambda/top.pdf
-- https://github.com/steshaw/lennart-lambda

import Text.PrettyPrint hiding(($$))
import Data.List(union,(\\))
import Data.IntMap(IntMap,(!))
import qualified Data.IntMap as Map

infixl 9 :$
type Name = Int
data Term = Var Name | Lam Name Type Term | Term :$ Term
    deriving (Eq, Ord)

infixl 8 $$
($$) :: Term -> [Term] -> Term
f $$ [] = f
f $$ (e:es) = f :$ e $$ es

lam :: [(Name,Type)] -> Term -> Term
lam [] e = e
lam ((x,t):xs) e = Lam x t (lam xs e)

-- Compute the free variables of an expression.

freeVars :: Term -> [Name]
freeVars (Var v) = [v]
freeVars (Lam v _ e) = freeVars e \\ [v]
freeVars (f :$ a) = freeVars f `union` freeVars a

instance Show Term where
     show = renderStyle style . ppLC 0

ppLC :: Int -> Term -> Doc
ppLC _ (Var v) = text $ show v
ppLC p (Lam v t e) = pparens (p>0) $ text ("\\" ++ show v ++ "::" ++ show t ++ ".") <> ppLC 0 e
ppLC p (f :$ a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d

tmI, tmK, tmS :: Term
tmI = Lam 1 (TyCon 1) (Var 1)
tmK = lam [(1,t 1), (2,t 2)] $ Var 1 where t = TyCon

tmS = lam [(1,t 2 :-> t 1 :-> t 0), (2,t 2 :-> t 1), (3,t 2)] (Var 1 :$ Var 3 :$ (Var 2 :$ Var 3))
      where t = TyCon

infixr 6 :->
data Type = TyCon Int | Type :-> Type deriving(Eq, Ord)

instance Show Type where
  show = renderStyle style . ppTy 0

ppTy :: Int -> Type -> Doc
ppTy _ (TyCon v) = text (show v)
ppTy p (a :-> r) = pparens (p>1) (ppTy 2 a <+> text ":->" <+> ppTy 1 r)

tyI, tyK, tyS :: Type
tyI = TyCon 1 :-> TyCon 1 
tyK = TyCon 1 :-> TyCon 2  :-> TyCon 1
tyS = (TyCon 2 :-> TyCon 1  :-> TyCon 0)
    :-> (TyCon 2 :-> TyCon 1) :-> (TyCon 2 :-> TyCon 0)


type Env = IntMap Type

emptyEnv :: Env
emptyEnv = Map.empty

typeOf :: Env -> Term -> Type
typeOf env (Var n) = env ! n 
typeOf env (Lam v t e) = t :-> typeOf (Map.insert v t env) e
typeOf env (f :$ a) = let {tf = typeOf env f; ta = typeOf env a}  in
  case tf of                      
    t1 :-> t2
        | ta == t1 -> t2
        | otherwise -> error (unwords["Expected type of",show a, "is", show t1,
                                      "actual:", show ta])
    _ -> error (unwords ["The term", show f, "has type",  show tf,
                         "which is not a function type"])

