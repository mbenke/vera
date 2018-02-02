module Base.Church(
  LC(..), ($$), lam, Term, Ty(..), Type
                  ) where
-- Borrowing some ideas from Augustsson's "Lambda Calculus Cooked 4 ways"
-- http://www.augustsson.net/Darcs/Lambda/top.pdf
-- https://github.com/steshaw/lennart-lambda

import Text.PrettyPrint hiding(($$))
import Data.List(union,(\\))

infixl 9 :$
data LC v t = Var v | Lam v t (LC v t) | (LC v t) :$ (LC v t)
    deriving (Eq)

infixl 8 $$
($$) :: LC v t -> [LC v t] -> LC v t
f $$ [] = f
f $$ (e:es) = f :$ e $$ es

lam :: [(v,t)] -> LC v t -> LC v t
lam [] e = e
lam ((x,t):xs) e = Lam x t (lam xs e)

-- Compute the free variables of an expression.

freeVars :: (Eq v) => LC v t -> [v]
freeVars (Var v) = [v]
freeVars (Lam v _ e) = freeVars e \\ [v]
freeVars (f :$ a) = freeVars f `union` freeVars a

instance (Show v, Show t) => Show (LC v t) where
     show = renderStyle style . ppLC 0

ppLC :: (Show v, Show t) => Int -> LC v t -> Doc
ppLC _ (Var v) = text $ show v
ppLC p (Lam v t e) = pparens (p>0) $ text ("\\" ++ show v ++ "::" ++ show t ++ ".") <> ppLC 0 e
ppLC p (f :$ a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d

type Term = LC Int Type

tmI = Lam 1 (TyVar 1) (Var 1)
tmK = lam [(1,t 1), (2,t 2)] $ Var 1 where t = TyVar

tmS = lam [(1,t 1), (2,t 2), (3,t 3)] (Var 1 :$ Var 3 :$ (Var 2 :$ Var 3))
      where t = TyVar

infixr 6 :->
data Ty v = TyVar v | Type :-> Type

instance (Show v) => Show (Ty v) where
  show = renderStyle style . ppTy 0

ppTy :: Show v => Int -> Ty v -> Doc
ppTy _ (TyVar v) = text (show v)
ppTy p (a :-> r) = pparens (p>1) (ppTy 2 a <+> text ":->" <+> ppTy 1 r)

type Type = Ty Int

tyI = TyVar 1 :-> TyVar 1 
tyK = TyVar 1 :-> TyVar 2  :-> TyVar 1
tyS = (TyVar 0 :-> TyVar 1  :-> TyVar 2)
    :-> (TyVar 0 :-> TyVar 1) :-> (TyVar 0 :-> TyVar 2)
