{-# LANGUAGE UndecidableInstances #-}

module Data.SBV.Depend where

import Data.SBV
import Data.SBV.Maybe qualified as SBV

import Data.SBV.Encode
import Data.SBV.Refine

import Base

class (Encode a, Ref (Arg a)) => Dep a where
  type Arg a :: Type
  dep :: Proxy a -> SBV (Sym (Arg a)) -> SBV (Sym a) -> SBool

newtype K k a = K { unK :: a }
  deriving newtype (Show, Eq, Ord, Enum, Num, Encode)

instance (Ref k, Ref a) => Dep (K k a) where
  type Arg (K k a) = k
  dep Proxy _ x = ref @a Proxy x

newtype Fin = Fin { unFin :: Natural }
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep Fin where
  type Arg Fin = Natural
  dep Proxy n x = x .>= 0 .&& x .< n

instance Dep Bool where
  type Arg Bool = ()
  dep Proxy _ _ = sTrue

instance Dep a => Dep (Maybe a) where
  type Arg (Maybe a) = Maybe (Arg a)
  dep Proxy x y = SBV.maybe (SBV.isNothing y)
    (\z -> SBV.maybe sFalse (dep @a Proxy z) y) x
