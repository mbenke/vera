module Lambda where
-- Borrowing some ideas from Augustsson's "Lambda Calculus Cooked 4 ways"
-- http://www.augustsson.net/Darcs/Lambda/top.pdf
-- https://github.com/steshaw/lennart-lambda


import Data.List(union,(\\))

infixl 9 :$
data LC v = Var v | Lam v (LC v) | (LC v) :$ (LC v)
    deriving (Eq)


-- Compute the free variables of an expression.

freeVars :: (Eq v) => LC v -> [v]
freeVars (Var v) = [v]
freeVars (Lam v e) = freeVars e \\ [v]
freeVars (App f a) = freeVars f `union` freeVars a
