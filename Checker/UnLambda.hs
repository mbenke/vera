module Checker.UnLambda where
import Text.PrettyPrint.ANSI.Leijen
-- untyped lambda, "not a number" approach
infixl 6 :$
type Name = String -- FIXME
data Expr = F Name -- Free
          | B Int  -- Bound
          | Expr :$ Expr
          | Abs Scope
          deriving (Show,Eq)

data Scope = Scope Expr deriving(Show,Eq)

abstract :: Name -> Expr -> Scope
abstract me expr = Scope (letmeB 0 expr) where
         letmeB :: Int -> Expr -> Expr
         letmeB this (F you) | you == me = B this
                             | otherwise = F you
         letmeB this (B that)            = B that
         letmeB this (fun :$ arg) = letmeB this fun :$ letmeB this arg
         letmeB this (Abs (Scope body)) = Abs $
                Scope (letmeB (this+1) body)

lam :: Name -> Expr -> Expr
lam n t = Abs (abstract n t)
lams :: [Name] -> Expr -> Expr
lams [] = id
lams (x:xs) = lam x . lams xs
comI = lam "x" (F "x")
comK = lams ["x", "y"] (F "x") 
comS = lama "x y z" $ (fx :$ fz) :$ (fy :$ fz) where [fx,fy,fz] = fria "x y z"
lama :: String -> Expr -> Expr
lama = lams . words
fria :: String -> [Expr]
fria = map F . words 

instantiate :: Expr -> Scope -> Expr
instantiate what (Scope body) = whatsB 0 body where
            whatsB this (B that) | this == that = what
                                 | otherwise = B that
            whatsB this (F you) = F you
            whatsB this (t :$ s) = whatsB this t :$ whatsB this s
            whatsB this  (Abs (Scope body)) = 
               Abs $ Scope (whatsB (this+1) body)

substitute :: Expr -> Name -> Expr -> Expr
substitute image me = instantiate image . abstract me
 
whnf ((Abs s) :$ t) = whnf $ instantiate t s
whnf e = e

nf(x :$ y) = case whnf x of
        Abs s -> nf $ instantiate y s
        _ -> nf x :$ nf y
nf(Abs (Scope y)) = Abs(Scope (nf y))
nf t = t
skk = (comS :$ comK) :$ comK

main = print $ nf skk