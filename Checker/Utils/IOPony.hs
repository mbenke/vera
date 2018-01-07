{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Utils.IOPony
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
import Data.IORef
import System.IO.Error
newtype Pony s a = Pony { unPony :: IORef s -> IO a }

runPony :: Pony s a -> s -> IO (a, IORef s)
runPony p s = do
        r <- newIORef s
        y <- unPony p r
        return (y,r)

instance Functor (Pony s) where
    fmap f (Pony p) = Pony $ \s -> fmap f (p s)

runPony0 :: Monoid s => Pony s a -> IO (a, IORef s)
runPony0 p = runPony p mempty      
evalPony p s = fmap fst (runPony p s)
evalPony0 :: Monoid s => Pony s a -> IO a
evalPony0 = fmap fst . runPony0


instance Monad (Pony s) where
  return a = Pony $ \s -> return a
  (Pony p) >>= k = Pony $ \s -> p s >>= \a -> unPony (k a) s

instance Applicative (Pony s) where
  pure = return
  (<*>) = ap

instance MonadState s (Pony s) where
  get = Pony $ \r -> readIORef r
  put s = Pony $ \r -> writeIORef r s

instance MonadError String (Pony s) where
  throwError e = Pony $ \_ -> throwError (userError e)
  catchError (Pony p) h = Pony $ \r -> catchError (h . ioeGetErrorString)

