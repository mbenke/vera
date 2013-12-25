{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module LambdaP.GenChecker where
import LambdaP.Core

import Data.List(union,(\\),nub)
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
--import Debug.Trace
import Data.Map(Map)
import qualified Data.Map as Map

freshNameFvs :: [Name] -> Name
freshNameFvs fvs = go 0 where
    go n = if v n `elem` fvs then go (n+1) else v n
    v k = "v" ++ show k

class HasVars a where
  freeNames :: a -> [Name]
  freshName :: a -> Name
  freshName = freshNameFvs . freeNames

  substT :: Name -> Type -> a -> a
  renameT :: Name -> Name -> a -> a
  renameT n n1 = substT n (Tvar n1)

  substM :: Name -> Term -> a -> a
  renameM :: Name -> Name -> a -> a
  renameM n n1 = substM n (Mvar n1)

  refreshWith :: (Map Name Name) -> [Name] -> a -> a
  refreshWith r ns = id

  refresh :: [Name] -> a -> a
  refresh = refreshWith Map.empty

  whnf :: a -> a
  whnf = id

  nf :: a -> a
  nf = id

  alphaEq :: a -> a -> Bool
  alphaEq _ _ = False

  betaEq :: a -> a -> Bool
  betaEq t1 t2 = alphaEq (nf t1) (nf t2)
{-
instance HasVars Name where
  freeNames n = [n]
  substT = undefined
  substM = undefined
-}

instance (HasVars a, HasVars b) => HasVars (a,b) where
  freeNames (a,b) = freeNames a `union` freeNames b
  substT n s = fmap (substT n s)
  substM n s = fmap (substM n s)
  whnf = fmap whnf
  alphaEq (a1,b1) (a2,b2) = alphaEq a1 a2 && alphaEq b1 b2
  betaEq (a1,b1) (a2,b2) = betaEq a1 a2 && betaEq b1 b2
  refreshWith r ns (a,b) = (refreshWith r ns a,refreshWith r ns b)

-- (n,t1,x) ~ bind n:t1 in x
instance HasVars a => HasVars (Name,Type,a) where
  freeNames (n,t,a) = freeNames t `union` (freeNames a \\ [n])
  substT n s t@(n1,t1,a)
      | n == n1 = (n1,substT n s t1,a)
      | n1 `elem` freeNames s = (n', substT n s t1, substT n s t')
      | otherwise = (n1, substT n s t1, substT n s a)
        where t' = renameM n1 n' a
              n' = freshName s
  substM n s t@(n1,t1,a)
      | n == n1 = (n1,substM n s t1,a)
      | n1 `elem` freeNames s = (n', substM n s t1, substM n s t')
      | otherwise = (n1, substM n s t1, substM n s a)
        where t' = renameM n1 n' a
              n' = freshName s

  alphaEq (n, t, k) (n', t', k')
    = alphaEq t t'  && alphaEq k (renameM n' n k')

  refreshWith r ns (n,t,k)
      | n `elem` ns = (n', t', refreshWith r' (n':ns) k)
      | otherwise = (n, t', refreshWith r (n:ns) k)
           where
                 n' = freshNameFvs ns
                 r' = Map.insert n n' r
                 t' = refreshWith r ns t
{-
instance HasVars a => HasVars [a] where
  freeNames = unionAll . map freeNames
  -- subst n xs ys = [subst n x y | x <- xs, y <- ys]
-}

uncurry3 :: (a->b->c->d) -> (a,b,c) -> d
uncurry3 f (a,b,c) = f a b c

instance HasVars Kind where
  freeNames Kstar = []
  freeNames (Kpi n t k) = freeNames t `union` (freeNames k \\ [n])

  substT _ _ Kstar = Kstar
  substT n s k@(Kpi n1 t1 k1) = uncurry3 Kpi $ substT n s (n1,t1,k1)
  substM _ _ Kstar = Kstar
  substM n s (Kpi n1 t1 k1) = Kpi n2 t2 k2 where
    (n2,t2,k2) = substM n s (n1,t1,k1)

  nf (Kpi x t k) = Kpi x (nf t) (nf k)
  nf k = k

  alphaEq Kstar Kstar = True
  alphaEq (Kpi n t k) (Kpi n' t' k')
    = alphaEq (n,t,k) (n,t',k')
  refreshWith r ns (Kpi n1 t1 k1) = Kpi n2 t2 k2 where
    (n2,t2,k2) = refreshWith r ns (n1,t1,k1)
  refreshWith r ns Kstar = Kstar

instance HasVars Type where
  freeNames (Tvar n) = [n]
  freeNames (Tall n t1 t2) = freeNames (n,t1,t2)
  freeNames (Tapp t1 t2) = freeNames (t1,t2)
  freeNames (Texi n t1 t2) = freeNames (n,t1,t2)
  freeNames (Tand t1 t2) = freeNames (t1,t2)
  freeNames (Tor t1 t2) = freeNames (t1,t2)
  freeNames Tbot = []

  substT n s t = sub t where
    sub t@(Tvar n1) = if n == n1 then s else  t
    sub t@(Tall n1 t1 t2) = uncurry3 Tall $ substT n s (n1,t1,t2)
    sub t@(Tapp t1 m) = uncurry Tapp $ substT n s (t1,m)
    sub t@(Texi n1 t1 t2) = uncurry3 Texi $ substT n s (n1,t1,t2)
    sub t@(Tand t1 t2) = Tand (sub t1) (sub t2)
    sub t@(Tor t1 t2) = Tor (sub t1) (sub t2)
    sub Tbot = Tbot

  substM n s t = sub t where
    sub t@(Tvar _) = t   -- substM does not touch Tvars
    sub t@(Tall n1 t1 t2) = uncurry3 Tall $ substM n s (n1,t1,t2)
    sub t@(Tapp t1 m) = Tapp (sub t1) (substM n s m)
    sub t@(Texi n1 t1 t2) = uncurry3 Texi $ substM n s (n1,t1,t2)
    sub t@(Tand t1 t2) = Tand (sub t1) (sub t2)
    sub t@(Tor t1 t2) = Tor (sub t1) (sub t2)
    sub Tbot = Tbot

  nf (Tapp t m) = Tapp (nf t) (nf m)
  nf (Tall n t1 t2) = Tall n (nf t1) (nf t2)
  nf t@(Tvar _) = t
  nf (Texi n t1 t2) = Texi n (nf t1) (nf t2)
  nf (Tand t1 t2) = Tand (nf t1) (nf t2)
  nf (Tor  t1 t2) = Tor (nf t1) (nf t2)
  nf Tbot = Tbot

  alphaEq (Tvar n) (Tvar n') = n == n'
  alphaEq (Tall n t s) (Tall n' t' s') = alphaEq t t'
                                       && alphaEq s (renameM n' n s')
  alphaEq (Tapp t m) (Tapp t' m') = alphaEq t t' && alphaEq m m'
  alphaEq (Texi n t s) (Texi n' t' s') = alphaEq (n,t,s) (n',t',s')
  alphaEq (Tand t1 t2) (Tand t1' t2') = alphaEq t1 t1' && alphaEq t2 t2'
  alphaEq (Tor t1 t2) (Tor t1' t2') = alphaEq t1 t1' && alphaEq t2 t2'
  alphaEq Tbot Tbot = True
  alphaEq _ _ = False

  refreshWith r ns t = sub t where
    sub t@(Tvar n) = case Map.lookup n r of
        Nothing -> t
        Just n' -> Tvar n'
    sub t@(Tall n1 t1 t2) = uncurry3 Tall $ refreshWith r ns (n1,t1,t2)
    sub t@(Tapp t1 m) = uncurry Tapp $ refreshWith r ns (t1,m)
    sub t@(Texi n1 t1 t2) = uncurry3 Texi $ refreshWith r ns (n1,t1,t2)
    sub t@(Tand t1 t2) = uncurry Tand $ refreshWith r ns (t1,t2)
    sub t@(Tor t1 t2) = uncurry Tor $ refreshWith r ns (t1,t2)
    sub t@Tbot = Tbot

unionAll :: Eq a => [[a]] -> [a]
unionAll = foldr union []

instance HasVars Term where
  freeNames (Mvar n) = [n]
  freeNames (Mapp m1 m2) = freeNames m1 `union` freeNames m2
  freeNames (Mlam n t1 m) = freeNames (n,t1,m)
  freeNames (Mwit t m1 m2) = freeNames (t,(m1,m2))
  freeNames (Mabs n1 t1 n2 t2 m1 m2) = -- TODO: check this
    unionAll [freeNames t1, freeNames t2, freeNames m1, freeNames m2 \\ [n1,n2]]
  freeNames (Mtup t m1 m2) = unionAll [freeNames t, freeNames m1, freeNames m2]
  freeNames (Mpi1 m) = freeNames m
  freeNames (Mpi2 m) = freeNames m
  freeNames (Min1 t m) = freeNames t `union` freeNames m
  freeNames (Min2 t m) = freeNames t `union` freeNames m
  freeNames (Mcas m (n1, t1, m1) (n2,t2,m2)) =
    freeNames (m,((n1, t1, m1), (n2,t2,m2)) )
  freeNames (Meps t m) = freeNames t `union` freeNames m

  substT n s t = sub t where
    fvs = freeNames s
    sub m@(Mvar _) = m -- substT does not touch Mvars
    sub m@(Mapp m1 m2) = Mapp (sub m1) (sub m2)
    sub m@(Mlam n1 t1 m1) = uncurry3 Mlam $ substT n s (n1,t1,m1)
    sub m@(Mwit t m1 m2) = Mwit t' m1' m2' where (t',(m1',m2')) = substT n s (t,(m1,m2))
    sub m@(Mabs n1 t1 n2 t2 m1 m2) = Mabs n1' t1' n2' t2' m1' m2' where
        fvs = freeNames s
        n1' = freshNameFvs fvs
        n2' = freshNameFvs (n1':fvs)
        t1' = substT n s t1
        t2' = substT n s t2
        m1' = sub m1
        m2' = sub . renameM n2 n2' . renameM n1 n1' $ m2
    sub m@(Mtup t m1 m2) = Mtup t' m1' m2' where (t',(m1',m2')) = substT n s (t,(m1,m2))
        -- (uncurry . uncurry $ Mtup) (substT n s ((t,m1),m2))
    sub m@(Mpi1 m1) = Mpi1 $ sub m1
    sub m@(Mpi2 m1) = Mpi2 $ sub m1
    sub m@(Min1 t1 m1) = uncurry Min1 $ substT n s (t1,m1)
    sub m@(Min2 t1 m1) = uncurry Min2 $ substT n s (t1,m1)
    sub m@(Mcas m1 c1 c2) = Mcas m1' c1' c2' where
      (m1',(c1',c2')) = substT n s (m1,(c1,c2))
    sub m@(Meps t1 m1) = uncurry Meps $ substT n s (t1,m1)

  substM n s t = sub t where
    fvs = freeNames s
    sub m@(Mvar n1) | n == n1  = s
                    | otherwise = m
    sub m@(Mapp m1 m2) = Mapp (sub m1) (sub m2)
    sub m@(Mlam n1 t1 m1) = uncurry3 Mlam $ substM n s(n1,t1,m1)

    sub m@(Mwit t m1 m2) = Mwit t' m1' m2' where
      (t',(m1',m2')) = substM n s (t,(m1,m2))
    sub m@(Mabs n1 t1 n2 t2 m1 m2) = Mabs n1' t1' n2' t2' m1' m2' where
        fvs = freeNames s
        n1' = freshNameFvs fvs
        n2' = freshNameFvs (n1':fvs)
        t1' = substM n s t1
        t2' = substM n s t2
        m1' = sub m1
        m2' = sub . renameM n2 n2' . renameM n1 n1' $ m2
    sub m@(Mtup t m1 m2) = Mtup t' m1' m2' where (t',(m1',m2')) = substM n s (t,(m1,m2))
        -- (uncurry . uncurry $ Mtup) (substT n s ((t,m1),m2))
    sub m@(Mpi1 m1) = Mpi1 $ sub m1
    sub m@(Mpi2 m1) = Mpi2 $ sub m1
    sub m@(Min1 t1 m1) = uncurry Min1 $ substM n s (t1,m1)
    sub m@(Min2 t1 m1) = uncurry Min2 $ substM n s (t1,m1)
    sub m@(Mcas m1 c1 c2) = Mcas m1' c1' c2'
      where (m1',(c1',c2')) = substM n s (m1,(c1,c2))
    sub m@(Meps t1 m1) = uncurry Meps $ substM n s (t1,m1)

  whnf (Mapp f a) = case whnf f of
    Mlam x t b -> whnf (substM x a b)
    f1 -> Mapp f1 a

  whnf (Mabs n1 t1 n2 t2 m1 m2) = case whnf m1 of
    (Mwit _ w1 w2) -> whnf $ substM n1 w1 $ substM n2 w2 $ m2
    m1' -> (Mabs n1 t1 n2 t2 m1' m2)

  whnf (Mpi1 m) = case whnf m of
    (Mtup _ m1 m2) -> whnf m1
    m' -> Mpi1 m'

  whnf (Mpi2 m) = case whnf m of
    (Mtup _ m1 m2) -> whnf m2
    m' -> Mpi2 m'

  -- [case inl q of inl n -> p] -->  p[n:=q]
  whnf (Mcas m c1 c2) = case whnf m of
    Min1 _ m1 -> applycase c1 m1
    Min2 _ m2 -> applycase c2 m2
    m' -> (Mcas m' c1 c2)
    where applycase (n,_,p) q = substM n q p

  whnf e = e

  nf (Mlam x t e) = Mlam x (nf t) (nf e)
  nf (Mapp f a) = case whnf f of
    Mlam x t b -> nf (substM x a b)
    f1 -> Mapp (nf f1) (nf a)
  nf m@(Mvar n) = m

  nf (Mwit t m1 m2) = Mwit (nf t) (nf m1) (nf m2)

  nf (Mabs n1 t1 n2 t2 m1 m2) = case whnf m1 of
    (Mwit _ w1 w2) -> nf $ substM n1 w1 $ substM n2 w2 $ m2
    m1' -> (Mabs n1 (nf t1) n2 (nf t2) (nf m1') (nf m2))

  nf (Mtup t m1 m2) = Mtup (nf t) (nf m1) (nf m2)

  nf (Mpi1 m) = case whnf m of
    (Mtup _ m1 m2) -> nf m1
    m' -> Mpi1 (nf m')

  nf (Mpi2 m) = case whnf m of
    (Mtup _ m1 m2) -> nf m2
    m' -> Mpi2 (nf m')

  nf (Min1 t m) = Min1 (nf t) (nf m)
  nf (Min2 t m) = Min2 (nf t) (nf m)

  nf (Mcas m c1 c2) = case whnf m of
    Min1 _ m1 -> nf(applycase c1 m1)
    Min2 _ m2 -> nf(applycase c2 m2)
    m' -> nf (Mcas m' c1 c2)
    where applycase (n,_,p) q = substM n q p

  nf (Meps t m) = Meps (nf t) (nf m)

  alphaEq (Mvar n) (Mvar n') = n == n'
  alphaEq (Mlam n t s) (Mlam n' t' s') = alphaEq t t'
                                       && alphaEq s (renameM n' n s')
  alphaEq (Mapp t m) (Mapp t' m') = alphaEq t t' && alphaEq m m'

  alphaEq (Mwit t m1 m2) (Mwit t' m1' m2') = alphaEq (t,(m1,m2)) (t,(m1',m2'))
  alphaEq (Mabs n1 t1 n2 t2 m1 m2)
          (Mabs n1' t1' n2' t2' m1' m2')
          =  alphaEq t1 t1'
          && alphaEq t2 t2'
          && alphaEq m1 m1'
          && alphaEq m2 (renameM n1' n1 (renameM n2' n2 m2'))

  alphaEq (Mtup t m1 m2) (Mtup t' m1' m2') = alphaEq (t,(m1,m2)) (t,(m1',m2'))
  alphaEq (Mpi1 m) (Mpi1 m') = alphaEq m m'
  alphaEq (Mpi2 m) (Mpi2 m') = alphaEq m m'
  alphaEq (Min1 t m) (Min1 t' m') = alphaEq t t' && alphaEq m m'
  alphaEq (Min2 t m) (Min2 t' m') = alphaEq t t' && alphaEq m m'

  alphaEq (Mcas m c1 c2) (Mcas m' c1' c2')
          =  alphaEq m m'
          && alphaEq c1 c1'
          && alphaEq c2 c2'

  alphaEq (Meps t m) (Meps t' m') = alphaEq t t' && alphaEq m m'

  alphaEq _ _ = False

-- Checker monad
type CM a = ErrorT String Identity a
runCM :: CM a -> Either String a
runCM = runIdentity . runErrorT

data IState = IState { isEnv :: Env }
type IM a = ErrorT String (StateT IState Identity) a
runIM m = runIdentity . runErrorT . runStateT m

reportError :: MonadError String  m => [String] -> m a
reportError = throwError . unwords

-- Environment
-- Mnemonic: Kinds on the Right
type Env = [(Name,Either Type Kind)]
lookupVar :: Name -> Env -> Maybe (Either Type Kind)
lookupVar = lookup

-- lookupTvar :: Env -> Name -> CM Kind
lookupTvar :: MonadError String m => Env -> Name -> m Kind
lookupTvar env n = case lookupVar n env of
  Just (Right k) -> return k
  Just (Left _) -> reportError ["Variable", n,"is an object variable"]
  Nothing -> reportError ["Undeclared type variable",n,"\nenv=",show env]

lookupMvar :: MonadError String m => Env -> Name -> m Type
lookupMvar env n = case lookupVar n env of
  Just (Left t) -> return t
  Just (Right _) -> reportError ["Variable", n,"is a type variable"]
  Nothing -> reportError ["Undeclared mvar",n,"\nenv=",show env]

insertMVar :: MonadError String m => Name -> Type -> Env -> m Env
insertMVar n t env = do
  checkType env t Kstar -- env |- t : *
  case lookup n env of
    Nothing -> return $ (n,Left t):env
    Just _ -> reportError ["Name",n,"already defined"]

insertTVar :: MonadError String m => Name -> Kind -> Env -> m Env
insertTVar n k env = do
  checkKind env k -- env |- k : []
  case lookup n env of
    Nothing -> return $ (n,Right k):env
    Just _ -> reportError ["Name",n,"already defined"]

emptyEnv :: Env
emptyEnv = []

-- | Check if a kind is well-formed wrt an environment
checkKind :: MonadError String m =>  Env -> Kind -> m ()
checkKind env Kstar = return ()
checkKind env (Kpi n t k) = do
  env' <- insertMVar n t env
  checkKind env' k

-- | Check if a type expression is of a specified kind
-- env |- t : k ?
checkType :: MonadError String m => Env -> Type -> Kind -> m ()
checkType env t k = do
  k' <- inferType env t
  if betaEq k k'
    then return ()
    else reportError ["Actual kind:",show k',
                      "\nis not equal to expected:",show k]

checkIsType env t = checkType env t Kstar

-- | Infer kind of a type expression
-- env |- t : ?
inferType :: MonadError String m => Env -> Type -> m Kind
inferType env (Tvar n) = lookupTvar env n
inferType env (Tall "_" t1 t2) = inferType env t2
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
checkTerm :: MonadError String m => Env -> Term -> Type -> m ()
checkTerm env m t = do
  t' <- inferTerm env m
  if betaEq t t'
    then return ()
    else reportError ["Actual type:",show t',
                      "\nis not equal to expected:",show t]

inferTerm :: MonadError String m => Env -> Term -> m Type
inferTerm env (Mvar n) = lookupMvar env n
inferTerm env (Mlam n t m) = do
  env' <- insertMVar n t env
  t' <- inferTerm env' m
  return (Tall n t t')

inferTerm env m@(Mapp m1 m2) = do
  tf <- inferTerm env m1
  case tf of
    Tall n t1 t2 -> do
      checkTerm env m2 t1 `catchError` handler
      return $ substM n m2 t2
        where
          handler e = reportError ["inferTerm ",show m,"\nWhen checking ",
                            show m2,":",show t1,"\n",e,
                            "\nEnv",unlines $ map show env]

    t -> reportError [show t, "is not a function type"] -- FIXME: better message
     
-- [m1,m2]_{∃ x:phi1.phi2}
inferTerm env (Mwit (Texi n t1 t2)  m1 m2) = do
  checkTerm env m1 t1
  checkTerm env (substM n m1 m2) (substM n m1 t2)
  return (Texi n t1 t2)

inferTerm env (Mwit t  m1 m2) =
  reportError ["Witness for a nonexistential type"]

-- abstract <n1:t1,n2:t2> = m1 in m2
inferTerm env m@(Mabs n1 t1 n2 t2 m1 m2) = do
  env' <- insertMVar n1 t1 env
  let t = (Texi n1 t1 t2)
  checkTerm env' m1 t `catchError` (h1 t)
  env'' <- insertMVar n2 t2 env'
  inferTerm env'' m2 `catchError` h2
     where
       h1 t e = reportError ["inferTerm ",show m,"\nWhen checking ",
                            show m1,":",show t,"\n",e]
       h2 e = reportError ["In ",show m,"\nIn ",show m2,"\n",e]

inferTerm env (Mtup t m1 m2)
  | (Tand t1 t2) <- nf t = do
    checkTerm env m1 t1
    checkTerm env m2 t2
    return t
  | otherwise = reportError ["Tuple not of and type"]

inferTerm env (Mpi1 m) = do
  t <- inferTerm env m
  case t of
    (Tand t1 t2) -> return t1
    _ -> reportError [show t, "is not a pair type"]

inferTerm env (Mpi2 m) = do
  t <- inferTerm env m
  case t of
    (Tand t1 t2) -> return t2
    _ -> reportError [show t, "is not a pair type"]

inferTerm env (Min1 t m)
  | Tor t1 t2 <- t = do
    checkTerm env m t1
    return t
  | otherwise = reportError ["in1 into",show t,"which is not disjunction"]

inferTerm env (Min2 t m)
  | Tor t1 t2 <- t = do
    checkTerm env m t2
    return t
  | otherwise = reportError ["in2 into",show t,"which is not disjunction"]

inferTerm env (Mcas m (n1,t1,m1) (n2,t2,m2)) = do
  checkTerm env m (Tor t1 t2)
  env1 <- insertMVar n1 t1 env
  t3 <- inferTerm env1 m1
  env2 <- insertMVar n2 t2 env
  checkTerm env2 m2 t3
  return t3

inferTerm env (Meps t m) = do
  checkTerm env m Tbot
  return t

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
-- for debugging, comment out instance above, uncomment below
--deriving instance Show Kind
instance Show Type where
  show (Tvar n) = n
  show (Tall _ t1 Tbot) = concat ["(~",show t1,")"]
  show (Tall n t1 t2)
    | n `elem` freeNames t2 = concat ["(!",n,":",show t1,")",show t2]
    | otherwise = concat ["(",show t1,"->", show t2,")"]
  show (Tapp t1 t2) = unwords [show t1,show t2]
  show (Texi n t1 t2) = concat ["(?",n,":",show t1,")",show t2]
  show (Tand t1 t2) = concat ["(",show t1,"&",show t2,")"]
  show (Tor t1 t2) = concat ["(",show t1,"|",show t2,")"]
  show (Tbot) = "$false"


-- FIXME: use showsPrec
paren s = concat["(",s,")"]
instance Show Term where
  show (Mvar n) = n
  show (Mapp t1 t2) = paren $ unwords [show t1,show t2]
  show (Mlam n t1 t2) = concat ["(","λ",n,":",show t1,".",show t2,")"]
  show (Mabs n1 t1 n2 t2 m1 m2) = concat [
    "(abstract <",n1,":",show t1,",",n2,":",show t2,"> =",show m1," in ",show m2,")"]
  show (Mtup t m1 m2) = concat ["<",show m1,",",show m2,">@",show t]
  show (Mwit t m1 m2) = concat ["[",show m1,",",show m2,"]@",show t]
  show (Mpi1 m) = paren $ unwords ["$p1", show m]
  show (Mpi2 m) = paren $ unwords ["$p2", show m]
  show (Min1 t m) = paren $ concat ["$i1@",show t,show m]
  show (Min2 t m) = paren $ concat ["$i2@",show t,show m]
  show (Mcas m (n1,t1,m1) (n2,t2,m2)) = unwords ["case",show m,"of {",
       "$i1",n1,":",show t1,"->",show m1,";",
       "$i2",n2,":",show t2,"->",show m2,"}"]