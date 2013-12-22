module Checker.Lambda where

infixl 6 :$
type Name = String -- FIXME
data Expr = V Name
          | Expr :$ Expr
          | Abs Name Expr
          deriving (Show,Eq)