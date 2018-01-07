module Lambda where
import Data.List(union,(\\))
data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
    deriving (Eq)


-- Compute the free variables of an expression.

freeVars :: (Eq v) => LC v -> [v]
freeVars (Var v) = [v]
freeVars (Lam v e) = freeVars e \\ [v]
freeVars (App f a) = freeVars f `union` freeVars a