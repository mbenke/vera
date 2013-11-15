module Prelambda.Utils where
import Prelambda.Preterm

dummy = "_"
karr = Kpi dummy
tarr = Tall dummy

mabs [] m = m
mabs (x:xs) m = Mabs x 0 (mabs xs m)
mapp ms = foldl1 Mapp ms

k0 = Kstar
k1 = karr 0 k0
t1 = tarr 0 0

-- Tests

m1 = Mabs "x" 0 (Mvar "x")
m2 = Mabs "y" 0 (Mvar "y")

mK = mabs ["x", "y"] (Mvar "x")
mKxy = mapp [mK, Mvar "x", Mvar "y"]

env0 = insertVar "0" k0 emptyEnv

test1 = checkKind emptyEnv k0
test2 = checkKind emptyEnv k1
test3 = checkType env0 t1
test4 = checkTerm env0 m1
test5 = subst "y" (Mvar "x") m1
test6 = whnf mKxy
test7 = nf mKxy

-- Boring

instance Num Preterm where
  fromInteger = Tvar . show
  (+) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
