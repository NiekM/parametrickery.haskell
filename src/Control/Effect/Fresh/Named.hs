{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Fresh.Named where

import Control.Monad.Fail as Fail
import Control.Monad.Fix
import Control.Monad.IO.Class
import Data.Kind
import Data.Map qualified as Map

import Control.Carrier.State.Strict
import Control.Algebra

import Base

data Fresh (m :: Type -> Type) a where
  Fresh :: Name -> Fresh m Nat

fresh :: Has Fresh sig m => Name -> m Nat
fresh t = send (Fresh t)

freshName :: Has Fresh sig m => Name -> m Name
freshName t = do
  n <- fresh t
  return $ t <> fromString (show n)

nominate :: Has Fresh sig m => Name -> a -> m (Named a)
nominate t x = do
  name <- freshName t
  return $ Named name x

newtype FreshC m a = FreshC { runFreshC :: StateC (Map Name Nat) m a }
  deriving newtype (Alternative, Applicative, Functor, Monad, Fail.MonadFail, MonadFix, MonadIO, MonadPlus)

evalFresh :: Functor m => FreshC m a -> m a
evalFresh (FreshC s) = evalState mempty s

instance Algebra sig m => Algebra (Fresh :+: sig) (FreshC m) where
  alg hdl sig ctx = FreshC case sig of
    L (Fresh t) -> do
      m <- get
      let n = fromMaybe 0 $ Map.lookup t m
      modify $ Map.insert t (n + 1)
      return (n <$ ctx)
    R other -> alg ((.runFreshC) . hdl) (R other) ctx
