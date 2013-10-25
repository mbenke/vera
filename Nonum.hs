-- McBride,McKinna "I am not a number"
module Nonum where

infixl 9 :$
infixr 6 :->

type Name = String -- FIXME
data Expr = F Name -- Free
          | B Int  -- Bound
          | Expr :$ Expr
          | Expr :-> Scope
          deriving (Show,Eq)

data Scope = Scope Expr deriving(Show,Eq)

abstract :: Name -> Expr -> Scope
abstract me expr = Scope (letmeB 0 expr) where
         letmeB this (F you) | you == me = B this
                             | otherwise = F you
         letmeB this (B that)            = B that
         letmeB this (fun :$ arg) = letmeB this fun :$ letmeB this arg
         letmeB this (domain :-> Scope body) = 
                letmeB this domain :-> Scope (letmeB (this+1) body)

instantiate :: Expr -> Scope -> Expr
instantiate what (Scope body) = whatsB 0 body where
            whatsB this (B that) | this == that = what
                                 | otherwise = B that
            whatsB this (F you) = F you
            whatsB this  (domain :-> Scope body) = 
                whatsB this domain :-> Scope (whatsB (this+1) body)

substitute :: Expr -> Name -> Expr -> Expr
substitute image me = instantiate image . abstract me