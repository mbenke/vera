{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Utils.Pony2
  ( Pony, runPony, runPony0, evalPony, evalPony0
  , MonadState(..), gets
  , MonadError(..)                   
  , Applicative(..), (<$>)
   ) where

import Control.Monad.Error.Class
import Control.Monad.State.Class
import Control.Monad.Identity
import Control.Applicative
import Data.Monoid
import Data.Either

newtype Pony s a = Pony { runPony :: s -> Either String (a, s) }
instance Functor (Pony s) where
    fmap f (Pony p) = Pony $ \s -> fmap (first f) (p s)
first  f (a,c) = (f a, c)
second f (c,b) = (c, f b)

runPony0 :: Monoid s => Pony s a -> Either String (a, s) 
runPony0 p = runPony p mempty      
evalPony p s = fmap fst (runPony p s)
evalPony0 :: Monoid s => Pony s a -> Either String a
evalPony0 = fmap fst . runPony0


instance Monad (Pony s) where
  return a = Pony $ \s -> Right (a,s)
  (Pony p) >>= k = Pony $ \s -> case (p s) of
     Right (a,s') -> runPony (k a) s'
     Left e -> Left e 

instance Applicative (Pony s) where
  pure = return
  (<*>) = ap

instance MonadState s (Pony s) where
  get = Pony $ \s -> Right (s,s)
  put s = Pony $ \_ -> Right ((),s)

instance MonadError String (Pony s) where
  throwError e = Pony $ \s -> Left e
  catchError (Pony p) h = Pony $ \s -> case p s of
    Left e -> runPony (h e) s
    Right q -> Right q
