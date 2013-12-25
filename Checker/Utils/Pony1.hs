{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Utils.Pony1
  (  Pony, runPony, runPony0, evalPony, evalPony0
  , MonadState(..), gets
  , MonadError(..)                   
  , Applicative(..), (<$>)

   ) where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative
import Data.Monoid

-- consider reordering monads?
newtype PonyT s m a = PonyT { unPonyT :: ErrorT String (StateT s m) a }
type Pony s a = PonyT s Identity a

runPonyT :: Monad m => PonyT s m a -> s -> m (Either String a, s)
runPonyT = runStateT . runErrorT . unPonyT

evalPonyT :: Monad m => PonyT s m a -> s -> m (Either String a)
evalPonyT = evalStateT . runErrorT . unPonyT
runPony m s = runIdentity (runPonyT m s)
evalPony m s = fst (runPony m s)

runPony0 :: Monoid s => Pony s a -> (Either String a, s) 
runPony0 m = runPony m mempty      

evalPony0 m = fst (runPony0 m)

instance Monad m => Monad (PonyT s m) where
  return  = PonyT . return
  (PonyT m) >>= k = PonyT (m >>= (unPonyT . k))
  
instance Functor m => Functor (PonyT s m) where 
  fmap f (PonyT m) = PonyT (fmap f m)

instance (Functor m, Monad m) => Applicative (PonyT s m) where
  pure = return
  (<*>) = ap
  
instance Monad m => MonadState s (PonyT s m) where
  get = PonyT get
  put = PonyT . put
  
instance Monad m => MonadError String (PonyT s m) where
  throwError = PonyT . throwError