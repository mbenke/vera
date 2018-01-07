-- untyped lambda, "not a number" approach
infixl 6 :$
type Name = String -- FIXME
data Expr = F Name -- Free
          | B Int  -- Bound
          | Expr :$ Expr
          | Abs Scope
          deriving (Show,Eq)

type Scope = Expr

abstract :: Name -> Expr -> Scope
abstract me expr = (letmeB 0 expr) where
         letmeB :: Int -> Expr -> Expr
         letmeB this (F you) | you == me = B this
                             | otherwise = F you
         letmeB this (B that)            = B that
         letmeB this (fun :$ arg) = letmeB this fun :$ letmeB this arg
         letmeB this (Abs body) = Abs $
                letmeB (this+1) body

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
instantiate what body = whatsB 0 body where
            whatsB this (B that) | this == that = what
                                 | otherwise = B that
            whatsB this (F you) = F you
            whatsB this (t :$ s) = whatsB this t :$ whatsB this s
            whatsB this  (Abs body) = 
               Abs $ whatsB (this+1) body

substitute :: Expr -> Name -> Expr -> Expr
substitute image me = instantiate image . abstract me

re t = red 0 t
red n ((Abs s) :$ t) = instantiate t s
red n ((x :$ y) :$ z) = red n (x :$ y) :$ z
red n (Abs t) = abstract xn (red (n+1) (instantiate (F xn) t)) where
    xn = "x" ++ show n
red n t = t
skk = (comS :$ comK) :$ comK

-- S = λ λ λ (2 0) (1 0)
-- K = λ λ 1
-- I = λ 0