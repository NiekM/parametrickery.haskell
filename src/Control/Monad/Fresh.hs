{- |
Module      : Control.Monad.Fresh
Copyright   : (c) Niek Mulleners 2024
Maintainer  : Niek Mulleners

A Monad transformer for generating fresh integers.

-}
module Control.Monad.Fresh
  ( FreshT
  , MonadFresh(..)
  , runFresh
  ) where

import Control.Monad.State

import Data.SBV.Internals

-- | A newtype around an integer state, used for generating fresh integers.
newtype FreshT m a = FreshT { getFreshT :: StateT Int m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans, MonadState Int)

-- | Evaluate a computation that generates fresh integers.
runFresh :: Monad m => FreshT m a -> m a
runFresh m = evalStateT (getFreshT m) 0

-- | Monads that support generating fresh integers.
class Monad m => MonadFresh m where
  fresh :: m Int

instance Monad m => MonadFresh (FreshT m) where
  fresh = do
    n <- get
    put $ n + 1
    return n

liftFresh :: Monad m => m a -> FreshT m a
liftFresh m = FreshT $ StateT \s -> (,s) <$> m

instance (Monad m, SolverContext m) => SolverContext (FreshT m) where
  constrain                 = liftFresh . constrain
  softConstrain             = liftFresh . softConstrain
  namedConstraint s         = liftFresh . namedConstraint s
  constrainWithAttribute xs = liftFresh . constrainWithAttribute xs
  setInfo x                 = liftFresh . setInfo x
  setOption                 = liftFresh . setOption
  setLogic                  = liftFresh . setLogic
  contextState              = liftFresh   contextState
