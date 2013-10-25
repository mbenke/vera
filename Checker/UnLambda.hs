-- untyped lambda, "not a number" approach

type Name = String -- FIXME
data Expr = F Name -- Free
          | B Int  -- Bound
          | Expr :$ Expr
          | Abs Scope
          deriving (Show,Eq)

abstract :: Name -> Expr -> Scope
abstract me expr = Scope (letmeB 0 expr) where
         letmeB :: Int -> Expr -> Expr
         letmeB this (F you) | you == me = B this
                             | otherwise = F you
         letmeB this (B that)            = B that
         letmeB this (fun :$ arg) = letmeB this fun :$ letmeB this arg
         letmeB this (Abs (Scope body)) = Abs $
                Scope (letmeB (this+1) body)

data Scope = Scope Expr deriving(Show,Eq)
