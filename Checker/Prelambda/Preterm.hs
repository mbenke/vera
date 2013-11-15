module Prelambda.Preterm where
import Data.List(union,(\\))
type Name = String
type Kind = Preterm
type Type = Preterm
type Term = Preterm
data Preterm = Kstar
          | Kpi Name Type Kind
          | Tvar Name
          | Tall Name Type Type
          | Tapp Type Term
          | Mvar Name
          | Mapp Term Term
          | Mabs Name Type Term
          deriving Eq


-- Substitution
freeVars :: Term -> [Name]
freeVars (Kstar) = []
freeVars (Kpi n t k) = freeVars t `union` (freeVars k \\ [n])
freeVars (Tvar n) = [n]
freeVars (Tall n t1 t2) = freeVars t1 `union` (freeVars t2 \\ [n])
freeVars (Tapp t1 t2) = freeVars t1 `union` freeVars t2
freeVars (Mvar n) = [n]
freeVars (Mapp t1 t2) = freeVars t1 `union` freeVars t2
freeVars (Mabs n t1 t2) = freeVars t1 `union` (freeVars t2 \\ [n])

-- find a variable not free in a given term
freshVar :: Term -> Name
freshVar t = freshVar' (freeVars t)
freshVar' :: [Name] -> Name
freshVar' fv = go 0 where
  go n = if v n `elem` fv then go (n+1) else v n
  v k = "v" ++ show k


subst :: Name -> Term -> Term -> Term
subst n s t = sub t where
    sub t@(Kpi n1 t1 k) | n == n1 = t
                        | n1 `elem` fvs = Kpi n' (sub t1) (sub k')
                        | otherwise = Kpi n1 (sub t1) (sub k)
                            where k' = subst n1 newVar k
                                  n' = freshVar t
                                  newVar = Mvar n'
                                  fvs = freeVars s
    sub t@(Mabs n1 t1 e) | n == n1 = t
                        | n1 `elem` fvs = Mabs n' (sub t1) (sub e')
                        | otherwise = Mabs n1 (sub t1) (sub e)
                            where e' = subst n1 newVar e
                                  n' = freshVar t
                                  newVar = Mvar n'
                                  fvs = freeVars s
    sub t@(Tall n1 t1 e) | n == n1 = t
                        | n1 `elem` fvs = Mabs n' (sub t1) (sub e')
                        | otherwise = Mabs n1 (sub t1) (sub e)
                            where e' = subst n1 newVar e
                                  n' = freshVar t
                                  newVar = Tvar n'
                                  fvs = freeVars s

    sub t@(Tapp t1 t2) = Tapp (sub t1) (sub t2)
    sub t@(Mapp t1 t2) = Mapp (sub t1) (sub t2)
    sub t@(Mvar n1) | n == n1 = s
                    | otherwise = t

    sub t@(Tvar n1) | n == n1 = s
                    | otherwise = t

    sub Kstar = Kstar

renameMvar n n' p = subst n (Mvar n') p
rename = renameMvar

alphaEq :: Preterm -> Preterm -> Bool
alphaEq Kstar Kstar = True
alphaEq (Kpi n t k) (Kpi n' t' k')
    = alphaEq t t'  && alphaEq k (rename n' n k')
alphaEq (Tvar n) (Tvar n') = n == n'
alphaEq (Mvar n) (Mvar n') = n == n'
alphaEq (Tall n t s) (Tall n' t' s') = alphaEq t t'
                                       && alphaEq s (rename n' n s')
alphaEq (Mabs n t s) (Mabs n' t' s') = alphaEq t t'
                                       && alphaEq s (rename n' n s')
alphaEq (Tapp t m) (Tapp t' m') = alphaEq t t' && alphaEq m m'
alphaEq (Mapp t m) (Mapp t' m') = alphaEq t t' && alphaEq m m'

alphaEq _ _ = False

whnf :: Preterm -> Preterm
whnf (Mapp f a) = case whnf f of
  Mabs x t b -> whnf (subst x a b)
  f1 -> Mapp f1 a
whnf e = e

nf :: Preterm -> Preterm
nf (Mabs x t e) = Mabs x (nf t) (nf e)
nf (Mapp f a) = case whnf f of
  Mabs x t b -> nf (subst x a b)
  f1 -> Mapp (nf f1) (nf a)
nf (Tapp t m) = Tapp (nf t) (nf m)
nf (Kpi x t k) = Kpi x (nf t) (nf k)
nf e = e

betaEq :: Preterm -> Preterm -> Bool
betaEq t1 t2 = alphaEq (nf t1) (nf t2)

-- Environment
type Env = [(Name,Type)]
emptyEnv :: Env
emptyEnv = []
lookupVar :: Name -> Env -> Maybe Type
lookupVar = lookup
insertVar :: Name -> Type -> Env -> Env
insertVar n t env = (n,t):env

-- Checking
type CheckResult a = a
reportError :: [String] -> CheckResult a
reportError = error . unwords
checkVar :: Env -> Name -> CheckResult Preterm
checkVar env n = case lookup n env of
     Just t -> t
     Nothing -> reportError ["ERROR: variable",n,"undefined"]


-- Kind formation (what kinds are ill-formed?)
checkKind :: Env -> Kind -> CheckResult ()
checkKind env Kstar = ()
checkKind env (Kpi n t k) = checkKind env' k where
          env' = insertVar n t env
checkKind env p = reportError ["ERROR:",show p,"not a kind"]

-- Kinding rules

checkType :: Env -> Type -> CheckResult Kind
checkType env (Tvar n) = let
     k = checkVar env n in
     if checkKind env k == ()
        then k
        else reportError ["bad type variable",n,show k, "is not a kind"]

checkType env (Tall n t1 t2) = let
      k = checkType (insertVar n t1 env) t2 in
      case k of
          Kstar -> Kstar
          k -> reportError ["ERROR:",show t2, "is not a type"]

checkType env pt@(Tapp phi m) = case
   checkType env phi of
     Kpi x t k -> let t1 = checkTerm env m in if t1 `betaEq` t
         then subst x m k
         else reportError ["Type mismatch for", show m,
                          "\nexpected:", show t,
                          "\n got:", show t1]

checkType env p = reportError ["ERROR:",show p,"is not a type"]

checkTerm :: Env -> Term -> CheckResult Type
checkTerm env (Mvar n) = let
     t = checkVar env n
     -- TODO: remove x fm env
     k = checkType env t
     in case k of
          Kstar -> t
          _ -> reportError ["Not a type:",show t]


checkTerm env (Mabs n t m) =
	  case checkType env t of
            Kstar -> let
              env' = insertVar n t env
	      t' = checkTerm env' m
	      in (Tall n t t')
	    _ -> reportError ["Not a type:",show t]

checkTerm env p = reportError ["ERROR:",show p,"is not a term"]

instance Show Preterm where
  show Kstar = "*"
  show (Kpi n t k) = concat["(",n,":",show t,")->",show k]
  show (Tvar n) = n
  show (Tall n t1 t2) = concat ["(∀",n,":",show t1,")",show t2]
  show (Tapp t1 t2) = unwords [show t1,show t2]
  show (Mvar n) = n
  show (Mapp t1 t2) = unwords [show t1,show t2]
  show (Mabs n t1 t2) = concat ["(","λ",n,":",show t1,".",show t2,")"]
