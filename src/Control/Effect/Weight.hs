{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Weight where

import Data.Monoid
import Control.Monad.Fail as Fail
import Control.Monad.Fix
import Control.Monad.IO.Class
import Data.Kind

import Control.Carrier.Writer.Strict
import Control.Algebra

import Base

data Weight (m :: Type -> Type) a where
  Weigh :: Nat -> Weight m ()

weigh :: Has Weight sig m => Nat -> m ()
weigh w = send (Weigh w)

newtype IgnoreC m a = IgnoreC { runIgnoreC :: m a }
  deriving newtype (Alternative, Applicative, Functor, Monad, Fail.MonadFail, MonadFix, MonadIO, MonadPlus)

ignoreWeight :: Functor m => IgnoreC m a -> m a
ignoreWeight (IgnoreC s) = s

instance Algebra sig m => Algebra (Weight :+: sig) (IgnoreC m) where
  alg hdl sig = case sig of
    L (Weigh _) -> pure
    R other     -> IgnoreC . alg ((.runIgnoreC) . hdl) other

newtype TallyC m a = TallyC { runTallyC :: WriterC (Sum Nat) m a }
  deriving newtype (Alternative, Applicative, Functor, Monad, Fail.MonadFail, MonadFix, MonadIO, MonadPlus)

tallyWeight :: Functor m => TallyC m a -> m (Nat, a)
tallyWeight (TallyC s) = first getSum <$> runWriter s

instance Algebra sig m => Algebra (Weight :+: sig) (TallyC m) where
  alg hdl sig ctx = TallyC case sig of
    L (Weigh w) -> do
      tell (Sum w)
      return ctx
    R other -> alg ((.runTallyC) . hdl) (R other) ctx
