{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module LambdaP.SpecChecker where
import LambdaP.Core

import Data.List(union,(\\),nub)
import Control.Monad.Error
import Control.Monad.Identity


class HasVars a where
  freeNames :: a -> [Name]
  freshName :: a -> Name
  freshName x = go 0 where
    fv = freeNames x
    go n = if v n `elem` fv then go (n+1) else v n
    v k = "v" ++ show k
  
  substT :: Name -> Type -> a -> a
  renameT :: Name -> Name -> a -> a
  renameT n n1 = substT n (Tvar n1)
  
  substM :: Name -> Term -> a -> a
  renameM :: Name -> Name -> a -> a
  renameM n n1 = substM n (Mvar n1)
  
  whnf :: a -> a
  whnf = id
  
  nf :: a -> a
  nf = id
  
  alphaEq :: a -> a -> Bool
  alphaEq _ _ = False
  
  betaEq :: a -> a -> Bool
  betaEq t1 t2 = alphaEq (nf t1) (nf t2)
  
instance HasVars Name where 
  freeNames n = [n]
  substT = undefined
  substM = undefined
  
{-
instance HasNames a => HasNames [a] where
  freeNames = concatMap freeNames
  -- subst n xs ys = [subst n x y | x <- xs, y <- ys]
-}  
instance HasVars Kind where
  freeNames Kstar = []
  freeNames (Kpi n t k) = freeNames t `union` (freeNames k \\ [n])

  substT _ _ Kstar = Kstar
  substT n s k@(Kpi n1 t1 k1) 
    | n == n1 = k
    | n1 `elem` freeNames s = Kpi n' (substT n s t1) (substT n s k')
    | otherwise = Kpi n1 (substT n s t1) (substT n s k1) 
        where k' = renameM n1 n' k1
              n' = freshName s
  substM _ _ Kstar = Kstar
  substM n s k@(Kpi n1 t1 k1) 
    | n == n1 = k
    | n1 `elem` freeNames s = Kpi n' (substM n s t1) (substM n s k')
    | otherwise = Kpi n1 (substM n s t1) (substM n s k1) 
        where k' = renameM n1 n' k1
              n' = freshName s
  
  nf (Kpi x t k) = Kpi x (nf t) (nf k)
  nf k = k
 
  alphaEq Kstar Kstar = True
  alphaEq (Kpi n t k) (Kpi n' t' k')
    = alphaEq t t'  && alphaEq k (renameM n' n k')

instance HasVars Type where
  freeNames (Tvar n) = [n]
  freeNames (Tall n t1 t2) = freeNames t1 `union` (freeNames t2 \\ [n])
  freeNames (Tapp t1 t2) = freeNames t1 `union` freeNames t2
  freeNames (Texi n t1 t2) = freeNames t1 `union` (freeNames t2 \\ [n])
  freeNames (Tand t1 t2) = freeNames t1 `union` freeNames t2
  freeNames (Tor t1 t2) = freeNames t1 `union` freeNames t2
  freeNames Tbot = []
  
  substT n s t = sub t where
    sub t@(Tvar n1) = if n == n1 then s else  t
    sub t@(Tall n1 t1 t2) 
       | n == n1 = t
       | n1 `elem` freeNames s = Tall n' (sub t1) (sub t')
       | otherwise = Tall n1 (sub t1) (sub t2)
          where t' = renameT n1 n' t2
                n' = freshName s
    sub t@(Tapp t1 m) = Tapp (sub t1) (substT n s m)
    sub t@(Texi n1 t1 t2) 
       | n == n1 = t
       | n1 `elem` freeNames s = Texi n' (sub t1) (sub t')
       | otherwise = Texi n1 (sub t1) (sub t2)
         where t' = renameT n1 n' t2
               n' = freshName s
    sub t@(Tand t1 t2) = Tand (sub t1) (sub t2)
    sub t@(Tor t1 t2) = Tor (sub t1) (sub t2)
    sub Tbot = Tbot

  substM n s t = sub t where 
    sub t@(Tvar _) = t   -- substM does not touch Tvars
    sub t@(Tall n1 t1 t2) 
      | n == n1 = t
      | n1 `elem` freeNames s = Tall n' (sub t1) (sub t')
      | otherwise = Tall n1 (sub t1) (sub t2)
        where t' = renameT n1 n' t2
              n' = freshName s
    sub t@(Tapp t1 m) = Tapp (sub t1) (substM n s m)
    sub t@(Texi n1 t1 t2) 
       | n == n1 = t
       | n1 `elem` freeNames s = Texi n' (sub t1) (sub t')
       | otherwise = Texi n1 (sub t1) (sub t2)
         where t' = renameT n1 n' t2
               n' = freshName s
    sub t@(Tand t1 t2) = Tand (sub t1) (sub t2)
    sub t@(Tor t1 t2) = Tor (sub t1) (sub t2)
    sub Tbot = Tbot

  nf (Tapp t m) = Tapp (nf t) (nf m)
  nf (Tall n t1 t2) = Tall n (nf t1) (nf t2)
  nf t@(Tvar _) = t

  alphaEq (Tvar n) (Tvar n') = n == n'
  alphaEq (Tall n t s) (Tall n' t' s') = alphaEq t t'
                                       && alphaEq s (renameM n' n s')
  alphaEq (Tapp t m) (Tapp t' m') = alphaEq t t' && alphaEq m m'

unionAll :: Eq a => [[a]] -> [a]
unionAll = foldr union []

instance HasVars Term where
  freeNames (Mvar n) = [n]
  freeNames (Mapp m1 m2) = freeNames m1 `union` freeNames m2
  freeNames (Mlam n t1 m) = freeNames t1 `union` (freeNames m \\ [n])
  freeNames (Mwit t m1 m2) = unionAll [freeNames t, freeNames m1, freeNames m2]
  freeNames (Mabs n1 t1 n2 t2 m1 m2) = -- TODO: check this
    unionAll [freeNames t1, freeNames t2, freeNames m1, freeNames m2 \\ [n1,n2]]
  freeNames (Mtup t m1 m2) = unionAll [freeNames t, freeNames m1, freeNames m2]
  freeNames (Mpi1 m) = freeNames m   
  freeNames (Mpi2 m) = freeNames m   
  freeNames (Min1 t m) = freeNames t `union` freeNames m
  freeNames (Min2 t m) = freeNames t `union` freeNames m
  freeNames (Mcas m (n1, t1, m1) (n2,t2,m2)) = unionAll
    [ freeNames m
    , freeNames t1 
    , freeNames m1 \\ [n1]
    , freeNames t2 
    , freeNames m2 \\ [n2]
    ]
      
  substT n s t = sub t where
    fvs = freeNames s
    sub m@(Mvar _) = m -- substT does not touch Mvars
    sub m@(Mapp m1 m2) = Mapp (sub m1) (sub m2)
    sub m@(Mlam n1 t1 m1) 
      | n == n1 = m 
      | n1 `elem` fvs = Mlam n' (substT n s t1) (sub m')
      | otherwise = Mlam n1 (substT n s t1) (sub m1)
        where m' = renameM n1 n' m1
              n' = freshName s
                    
  substM n s t = sub t where
    fvs = freeNames s
    sub m@(Mvar n1) | n == n1  = s
                    | otherwise = m
    sub m@(Mapp m1 m2) = Mapp (sub m1) (sub m2)
    sub m@(Mlam n1 t1 m1) 
      | n == n1 = m 
      | n1 `elem` fvs = Mlam n' (substM n s t1) (sub m')
      | otherwise = Mlam n1 (substM n s t1) (sub m1)
        where m' = renameM n1 n' m1
              n' = freshName s
  
  whnf (Mapp f a) = case whnf f of
    Mlam x t b -> whnf (substM x a b)
    f1 -> Mapp f1 a
  whnf e = e
  
  nf (Mlam x t e) = Mlam x (nf t) (nf e)
  nf (Mapp f a) = case whnf f of
    Mlam x t b -> nf (substM x a b)
    f1 -> Mapp (nf f1) (nf a)
  nf m@(Mvar n) = m

  alphaEq (Mvar n) (Mvar n') = n == n'
  alphaEq (Mlam n t s) (Mlam n' t' s') = alphaEq t t'
                                       && alphaEq s (renameM n' n s')
  alphaEq (Mapp t m) (Mapp t' m') = alphaEq t t' && alphaEq m m'
                                      
-- Checker monad
type CM a = ErrorT String Identity a
runCM :: CM a -> Either String a
runCM = runIdentity . runErrorT

reportError :: [String] -> CM a
reportError = throwError . unwords

-- Environment
-- Mnemonic: Kinds on the Right  
type Env = [(Name,Either Type Kind)]
lookupVar :: Name -> Env -> Maybe (Either Type Kind)
lookupVar = lookup

lookupTvar :: Env -> Name -> CM Kind
lookupTvar env n = case lookupVar n env of
  Just (Right k) -> return k
  Just (Left _) -> reportError ["Variable", n,"is an object variable"]
  Nothing -> reportError ["Undeclared variable",n]

lookupMvar :: Env -> Name -> CM Type
lookupMvar env n = case lookupVar n env of
  Just (Left t) -> return t
  Just (Right _) -> reportError ["Variable", n,"is a type variable"]
  Nothing -> reportError ["Undeclared variable",n]

insertMVar :: Name -> Type -> Env -> CM Env
insertMVar n t env = do
  checkType env t Kstar -- env |- t : *
  case lookup n env of
    Nothing -> return $ (n,Left t):env  
    Just _ -> reportError ["Name",n,"already defined"]

insertTVar :: Name -> Kind -> Env -> CM Env
insertTVar n k env = do
  checkKind env k -- env |- k : []
  case lookup n env of
    Nothing -> return $ (n,Right k):env  
    Just _ -> reportError ["Name",n,"already defined"]

emptyEnv :: Env
emptyEnv = []

-- | Check if a kind is well-formed wrt an environment
checkKind :: Env -> Kind -> CM ()
checkKind env Kstar = return ()
checkKind env (Kpi n t k) = do
  env' <- insertMVar n t env
  checkKind env' k
  
-- | Check if a type expression is of a specified kind
-- env |- t : k ?
checkType :: Env -> Type -> Kind -> CM ()
checkType env t k = do 
  k' <- inferType env t
  if betaEq k k' 
    then return ()
    else reportError ["Actual kind:",show k',
                      "\nis not equal to expected:",show k]
         
checkIsType env t = checkType env t Kstar

-- | Infer kind of a type expression
-- env |- t : ?
inferType :: Env -> Type -> CM Kind
inferType env (Tvar n) = lookupTvar env n
inferType env (Tall n t1 t2) = do
  env' <- insertMVar n t1 env
  inferType env' t2
inferType env (Tapp t m) = do
  k <- inferType env t
  case k of
     Kpi x t1 k1 -> do
       checkTerm env m t1
       return $ substM x m k1
     Kstar -> reportError ["checkType Tapp: expected product kind"]
inferType env (Texi n t1 t2) = do
  env' <- insertMVar n t1 env
  inferType env' t2
inferType env (Tand t1 t2) = mapM_ (checkIsType env) [t1,t2] >> return Kstar
inferType env (Tor t1 t2) = mapM_ (checkIsType env) [t1,t2] >> return Kstar
inferType env Tbot = return Kstar

-- | Check if a term is of a specified type
-- env |- m : t ?
checkTerm :: Env -> Term -> Type -> CM ()
checkTerm env m t = do 
  t' <- inferTerm env m
  if betaEq t t' 
    then return ()
    else reportError ["Actual type:",show t',
                      "\nis not equal to expected:",show t]
         
inferTerm :: Env -> Term -> CM Type
inferTerm env (Mvar n) = lookupMvar env n
inferTerm env (Mlam n t m) = do
  env' <- insertMVar n t env
  t' <- inferTerm env' m
  return (Tall n t t')
  
inferTerm env (Mapp m1 m2) = do
  tf <- inferTerm env m1
  case tf of
    Tall n t1 t2 -> do
      checkTerm env m2 t1
      return $ substM n m2 t2
    t -> reportError [show t, "is not a function type"] -- FIXME: better message
    
-- Utils & Tests
  
dummy = "_"
karr = Kpi dummy 
tarr = Tall dummy

k0 = Kstar
k1 = karr 0 k0
t1 = tarr 0 0
m1 = Mlam "x" 0 (Mvar "x")

mabs [] m = m
mabs (x:xs) m = Mlam x 0 (mabs xs m)
mapp ms = foldl1 Mapp ms
mK = mabs ["x", "y"] (Mvar "x")
mKxy = mapp [mK, Mvar "x", Mvar "y"]
-- >>> test5
-- (λv0:0.x)
test5 = substM "y" (Mvar "x") m1
-- >>> test6
-- x
test6 = whnf mKxy
-- >>> test7
-- x
test7 = nf mKxy

env0 :: Env
env0 = [("0",Right k0)] -- insertTVar "0" k0 emptyEnv

test1 = runCM $ checkKind emptyEnv k0

test2 = runCM $ checkKind env0 k1
test3 = runCM $ inferType env0 t1
test4 = runCM $ inferTerm env0 m1

-- Boring
instance Num Type where
  fromInteger = Tvar . show
  (+) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  

instance Show Kind where            
  show Kstar = "*"
  show (Kpi n t k) 
    | n `elem` freeNames k = concat["(",n,":",show t,")->",show k]
    | otherwise =  concat ["(",show t,"->", show k,")"]

instance Show Type where
  show (Tvar n) = n
  show (Tall n t1 t2)  
    | n `elem` freeNames t2 = concat ["(∀",n,":",show t1,")",show t2]
    | otherwise = concat ["(",show t1,"->", show t2,")"]
  show (Tapp t1 t2) = unwords [show t1,show t2]
  
instance Show Term where
  show (Mvar n) = n
  show (Mapp t1 t2) = unwords [show t1,show t2] 
  show (Mlam n t1 t2) = concat ["(","λ",n,":",show t1,".",show t2,")"]

  
