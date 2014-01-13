{-# LANGUAGE Rank2Types, NoMonomorphismRestriction #-}
module Examples where
import LambdaP.Core
import LambdaP.GenChecker

import Utils.Pony2 -- "I want a pony" ;)
-- import qualified Utils.Lens as Lens
import Utils.Lens -- (SimpleLens, lens,(^.),(%~),(^~))
import Control.Monad(liftM2)
import Data.Monoid

import Control.Monad.State.Class
(%=) :: MonadState s m => SimpleLens s a -> (a->a) -> m ()
l %= f = modify (l %~ f)

(.=) :: MonadState s m => SimpleLens s a -> a -> m ()
l .= c = l %= const c

use :: MonadState s m => SimpleLens s a -> m a
use l = gets (^.l)

data TState = TState { _output :: [String], _tsEnv :: Env, _tsCnt :: Int, 
                       _tsGoals :: [Goal], _tsCurrent :: Name, _tsTerm :: Term}

type StateLens b = SimpleLens TState b
tsTerm :: SimpleLens TState Term
tsTerm = lens _tsTerm (\s v -> s { _tsTerm = v })
tsGoals :: StateLens [Goal]
tsGoals = lens _tsGoals (\s v -> s { _tsGoals = v })
tsCnt = lens _tsCnt (\s v -> s { _tsCnt = v })

-- Special form for 'no proof'
emptyTerm :: Term
emptyTerm = (Mvar emptyName)
emptyName = ""

instance Monoid TState where
  mempty = TState [] [] 0 [] "" emptyTerm
  mappend = error "mappend@TState: you are not supposed to do that"  

writeln :: String -> TM ()  
writeln l = modify $ \s -> s { _output = l:_output s }
type TM a = Pony TState a
-- runTM m = runPony

tick :: TM Int
tick = do
  state <- get
  let cnt = _tsCnt state
  put state { _tsCnt = cnt + 1 }
  return cnt

getEnv :: TM Env 
getEnv = gets _tsEnv

getCurrent :: TM Name
getCurrent = gets _tsCurrent
setCurrent :: Name -> TM ()
setCurrent n = modify $ \s -> s { _tsCurrent = n }

getGoals :: TM [Goal]
getGoals = use tsGoals

getGoal = do
  gs <- getGoals
  case gs of
     [] -> throwError "no unproven goals"  
     (g:_) -> return g

popGoal = do
  gs <- getGoals
  case gs of
     [] -> throwError "no unproven goals"  
     (g:gs) -> do
       tsGoals .= gs
       return g

pushGoal :: Goal -> TM ()
pushGoal g = modify $ tsGoals %~ (g:) -- \s -> s { _tsGoals = g:_tsGoals s }

addToEnv :: (Name,Either Type Kind) -> TM ()
addToEnv pair = do
  state <- get
  put state { _tsEnv = pair: _tsEnv state }

addProp :: Name -> TM Type
addProp a = addToEnv (a,Right Kstar) >> return (Tvar a)

addProps :: [Name] -> TM [Type]
addProps = mapM addProp

newVar' :: String -> TM Name
newVar' s = (s++) . show <$> tick 

wildTick = newVar' "_"

checkTermTM m t = do
  env <- getEnv
  checkTerm env m t

inferTypeTM t = do
  env <- getEnv
  inferType env t
  
inferTermTM t = do
  env <- getEnv
  inferTerm env t

(.->.) :: Type -> Type ->  Type
p .->. q = Tall "_" p q 

(/\) :: Type -> Type -> Type
(/\) = Tand

(\/) :: Type -> Type -> Type
(\/) = Tor

π1 = Mpi1
π2 = Mpi2


--hlam :: Type -> (Term -> Term) -> Name -> Term
--hlam t mf n = Mlam n t (mf (Mvar n))

hlam :: Name -> Type -> (Term -> Term) -> Term
hlam n t mf = Mlam n t (mf (Mvar n))

fun = hlam
--fun1 :: Name -> Type -> Term -> Term

and_ind  :: (Term -> Term -> Term) -> Term -> Term
and_ind f q = f (Mpi1 q) (Mpi2 q)

conj :: Type -> Type -> Term -> Term -> Term
conj a b = Mtup (a /\ b)

tyvars :: String -> [Type]
tyvars = map Tvar . words 

prop :: Name -> TM Type
prop a = do
  env <- getEnv
  case lookupVar a env of
    Nothing -> addProp a
    -- Just (Right Kstar) -> return (Tvar a)
    Just _ -> throwError (a ++ " already defined")
    
props :: String -> TM [Type]
props = mapM prop . words

mkArity :: [Type] -> Kind
mkArity [] = Kstar
mkArity (t:ts) = Kpi "_" t (mkArity ts)

predicate :: Name -> [Type] -> TM Type
predicate p ts = do
  let kind = mkArity ts
  addToEnv (p,Right kind) 
  return (Tvar p)

mvars :: String -> [Term]
mvars = map Mvar . words 

neg,negneg :: Type -> Type
neg a = a .->. Tbot
negneg = neg . neg

p01 = hlam "h" (a /\ b) (\h -> and_ind elim h) where
  -- elim =  fun "H0" a (\h0 -> (fun "H1" b (\h1 -> conj b a h1 h0)))
  elim = \h0 h1 -> Mlam "H0" a $ Mlam "H1" b $ conj b a h1 h0
  -- [h,h0,h1] = mvars "h h0 h1"
  [a,b] = tyvars "a b"

{-
Variable A B :Prop.
Theorem example01 : A /\ B -> B /\ A.
firstorder.
Qed.
Print example01.
example01 = 
fun H : A /\ B =>
@and_ind A B (B /\ A) (fun (H0 : A) (H1 : B) => @conj B A H1 H0) H
     : A /\ B -> B /\ A
-}
data Goal = G Env Name Type
addGoal name typ = do
  env <- getEnv
  let g = G env name typ
  pushGoal g
  setCurrent name
  return name

newGoal typ = do
  name <- newVar' "?"
  addGoal name typ

intro1 :: Name -> TM ()
intro1 h = do
  G env name typ <- popGoal
  case whnf typ of
       Tall x t1 t2 -> undefined
  
e1 = do
  [a,b] <- props "a b"
  let f01 = (Tand a b) .->.  (Tand b a)
  -- let elim h0 h1 = conj b a h1 h0
  -- let p01 = hlam "h" (a /\ b) (\h -> and_ind (\h0 h1 -> conj b a h1 h0) h)
  env <- getEnv
  g <- addGoal "?1" f01
  let env' = ("?1",Left f01):env
  let p01 = Mvar "?1" 
  writeln (show p01)
  -- inferType env f01
  -- inferTerm env p01
  checkTerm env' p01 f01
  inferTerm env' p01
e01 = do
  [a,b] <- props "a b"
  let f01 = (Tand a b) .->.  (Tand b a)
  let elim h0 h1 = conj b a h1 h0
  let p01 = hlam "h" (a /\ b) (\h -> and_ind (\h0 h1 -> conj b a h1 h0) h)
  env <- getEnv
  -- inferType env f01
  -- inferTerm env p01
  checkTerm env p01 f01

test01 = evalPony0 e01 


-- false_ind a : False -> a 
false_ind :: Type -> Term -> Term
false_ind t m = Meps t m
false = Tbot

e06 :: TM Type
e06 = do
  a <- prop "a"
  let nnaa =  negneg a .->. a
  inferTypeTM nnaa
  let f06a = neg nnaa
  let f06 = neg f06a
  let p06a = fun "h" f06a $ 
            (\h -> 
             (fun "h0" false (\h0 -> (fun "h1" false (\h1 -> h1)) `Mapp` h0)) `Mapp`
             ((fun "h0" nnaa (\h0 -> Mapp h h0)) `Mapp` 
             ((fun "h0" (neg a) 
              (\h0 -> 
                fun "h1" (negneg a) 
                (\h1 -> (fun "H2" false (\h2 -> false_ind a h2)) `Mapp`
                        (Mapp h1 h0)
                )
              )
             ) `Mapp`
             (fun "h0" a (\h0 -> h `Mapp` fun "_" (negneg a) (const h0)))
             ))
            )

  let p06b = fun "h" f06a $ 
            (\h -> 
             
             ((fun "h0" nnaa (\h0 -> Mapp h h0)) `Mapp` 
             ((fun "h0" (neg a) 
              (\h0 -> 
                fun "h1" (negneg a) 
                (\h1 -> (fun "H2" false (\h2 -> false_ind a h2)) `Mapp`
                        (Mapp h1 h0)
                )
              )
             ) `Mapp`
             (fun "h0" a (\h0 -> h `Mapp` fun "_" (negneg a) (const h0)))
             ))
            )
              
  env <- getEnv
  let envNames = fmap fst env
  let p06 = refresh envNames p06a

  checkTermTM p06a f06
  checkTermTM p06b f06
  inferTermTM p06
  
{-
Theorem example_06 : ~~(~~A -> A).
firstorder.
Qed.
Print example_06.
example_06 = 
fun H : ~ (~ ~ A -> A) =>
(fun H0 : False => (fun H1 : False => H1) H0)
  ((fun H0 : ~ ~ A -> A => H H0)
     ((fun (H0 : A -> False) (H1 : ~ ~ A) =>
       (fun H2 : False => False_ind A H2) (H1 H0))
        (fun H0 : A => H (fun _ : ~ ~ A => H0))))
     : ~ ~ (~ ~ A -> A)
-}

{-
Variable o: Prop.
Variable P : o -> Prop.
Theorem example_07 : (forall x, P(x)) -> forall y, P(y).

firstorder.
Qed.
Print example_07.

example_07 = 
fun H : forall x : o, P x => H
     : (forall x : o, P x) -> forall y : o, P y
-}

forall, exists :: Name -> TM Type -> TM Type -> TM Type
forall n = liftM2 (Tall n)
exists n = liftM2 (Texi n)

bind :: (Name -> Type -> a -> a) -> Name -> Type -> (Term->a) -> a 
bind con n t f = con n t (f (Mvar n))

hall, hexi :: Name -> Type -> (Term -> Type) -> Type
hall = bind Tall
hexi = bind Texi

e07 = do
  o <- prop "o"
  p <- predicate "P" [o]
  let pe x = Tapp p x
  let f07 = (hall "x" o  pe) .->. (hall "y" o pe)
  inferTypeTM f07 
  let p07 = fun "H" (hall "z" o  pe) id
  checkTermTM p07 f07 
  inferTermTM p07
  
  
{-
Theorem example_13 : (exists x, P(x)) -> exists y, P y.
intro H.
elim H.
intros z H1.
exists z.
exact H1.
Qed.
Print example_13.
example_13 = 
fun H : exists x : o, P x =>
ex_ind (fun (z : o) (H1 : P z) => ex_intro (fun y : o => P y) z H1) H
     : (exists x : o, P x) -> exists y : o, P y
-}

e13 = do 
  o <- prop "o"
  p <- predicate "P" [o]
  let pe x = Tapp p x  
  let f13 = (hexi "x" o  pe) .->. (hexi "y" o pe)    
  inferTypeTM f13 
  -- let p13 = fun "H" (hexi "z" o  pe) id
  let p13 = fun "H" (hexi "z" o  pe) $
            \h -> ex_ind o pe 
                   (\z h1 -> ex_intro "y" o (\y -> (pe y)) z h1)
                 h 
     
  checkTermTM p13 f13 
  inferTermTM p13
  

ex_ind :: Type -> (Term -> Type) -> (Term -> Term -> Term) -> Term -> Term
ex_ind t1 ft2 fm1 m2 = Mabs "z1" t1  "z2" (ft2 (Mvar "z1")) m2 (fm1 (Mvar "z1") (Mvar "z2"))

ex_intro :: Name -> Type -> (Term -> Type) -> Term -> Term -> Term
ex_intro x t1 ft2 = Mwit (Texi x t1 (ft2 (Mvar x)))
run :: TM a -> IO a
run p = case runPony0 p of
  Left e -> error ('\n':e)
  Right (v,s) -> do
        putStrLn  . unlines . reverse . _output $ s
        return v


hexi2 :: Name -> Type -> (Term -> TM Type) -> TM Type
hexi2 n t f = Texi n t <$> (f $ Mvar n)

{-
Coq < Theorem example_12 : (exists x, ~P(x)) -> ~forall x, P(x).
example_12 < firstorder.
No more subgoals.
example_12 < Show Proof.
(fun H : exists x : o, ~ P x =>
 (fun H0 : forall x : o, P x =>
  ex_ind
    (fun (x : o) (H1 : ~ P x) =>
     (fun H2 : P x => (fun H3 : False => H3) (H1 H2)) (H0 x)) H)
 :~ (forall x : o, P x))
-}
-- ex_ind :: Type -> (Term -> Type) -> (Term -> Term -> Term) -> Term -> Term
e12 = do
  o <- prop "o"
  p <- predicate "P" [o]
  let pe x = Tapp p x 
  let f12a = (hexi "x" o (\x  -> neg $ pe x))
  let f12b = hall "x" o pe
  let f12 = f12a .->. neg f12b
  inferTypeTM f12
  let p12 = fun "H" f12a (\h ->
         fun "H0" f12b (\h0 ->
         ex_ind
           (o::Type)
           (\x -> neg (pe x){-::Term->Type-})
           (\x h1 ->
             (Mapp 
               (fun "H2" (pe x) $ \h2 ->
                (Mapp
                 (fun "H3" Tbot $ \h3 -> h3)
                 (Mapp h1 h2)
                )
               )
               (Mapp h0 x)
             )
           )
           h
         ))
  let p12' = fun "H" f12a (\h ->
         fun "H0" f12b (\h0 ->
         ex_ind
           (o::Type)
           (\x -> neg (pe x){-::Term->Type-})
           (\x h1 ->
             (Mapp 
               (fun "H2" (pe x) $ \h2 ->
                 (Mapp h1 h2)
               )
               (Mapp h0 x)
             )
           )
           h
         ))
  let p12'' = fun "H" f12a (\h ->
         fun "H0" f12b (\h0 ->
         ex_ind
           (o::Type)
           (\x ->neg (pe x){-::Term->Type-})
           (\x h1 ->
             (Mapp 
               h1
               (Mapp h0 x)
             )
           )
           h
         ))
  checkTermTM p12 f12
  checkTermTM p12' f12
  checkTermTM p12'' f12
  inferTermTM p12
