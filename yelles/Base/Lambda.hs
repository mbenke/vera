module Base.Lambda(LC(..), ($$), freeVars, ppLC, Term) where
-- Borrowing some ideas from Augustsson's "Lambda Calculus Cooked 4 ways"
-- http://www.augustsson.net/Darcs/Lambda/top.pdf
-- https://github.com/steshaw/lennart-lambda

import Text.PrettyPrint hiding(($$))
import Data.List(union,(\\))

infixl 9 :$
data LC v = Var v | Lam v (LC v) | (LC v) :$ (LC v)
    deriving (Eq)

infixl 8 $$
($$) :: LC v -> [LC v] -> LC v
f $$ [] = f
f $$ (e:es) = f :$ e $$ es

lam :: [v] -> LC v -> LC v
lam [] t = t
lam (x:xs) t = Lam x (lam xs t)

-- Compute the free variables of an expression.

freeVars :: (Eq v) => LC v -> [v]
freeVars (Var v) = [v]
freeVars (Lam v e) = freeVars e \\ [v]
freeVars (f :$ a) = freeVars f `union` freeVars a

instance (Show v) => Show (LC v) where
     show = renderStyle style . ppLC 0

ppLC :: (Show v) => Int -> LC v -> Doc
ppLC _ (Var v) = text $ show v
ppLC p (Lam v e) = pparens (p>0) $ text ("\\" ++ show v ++ ".") <> ppLC 0 e
ppLC p (f :$ a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d

type Term = LC Int

tmI = Lam 1 (Var 1)
tmK = Lam 1 $ Lam 2 $ Var 1

tmS = lam [1,2,3] (Var 1 :$ Var 3 :$ (Var 2 :$ Var 3))

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
