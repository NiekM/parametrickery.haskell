{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module Sugar where

import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Compose
import Data.Coerce

type One = Const ()

type family Coated f a where
  Coated Identity        a = a
  Coated (Const k)       a = k
  Coated (Product f g)   a = (Coated f a, Coated g a)
  Coated (Sum     f g)   a = Either (Coated f a) (Coated g a)
  Coated (Compose f g)   a = Coated f (Coated g a)
  Coated f               a = f a

class Sugar f where
  sugar   ::        f a -> Coated f a
  desugar :: Coated f a ->        f a

  default sugar :: (f a ~ Coated f a) => f a -> Coated f a
  sugar = coerce

  default desugar :: (f a ~ Coated f a) => Coated f a -> f a
  desugar = coerce

instance Sugar Identity where
  sugar = runIdentity
  desugar = Identity

instance Sugar (Const k) where
  sugar = getConst
  desugar = Const

instance (Sugar f, Sugar g) => Sugar (Product f g) where
  sugar (Pair x y) = (sugar x, sugar y)
  desugar (x, y)= Pair (desugar x) (desugar y)

instance (Sugar f, Sugar g) => Sugar (Sum f g) where
  sugar (InL x) = Left (sugar x)
  sugar (InR y) = Right (sugar y)
  desugar (Left x) = InL (desugar x)
  desugar (Right y) = InR (desugar y)

instance (Sugar f, Sugar g, Functor f) => Sugar (Compose f g) where
  sugar = sugar . fmap sugar . getCompose
  desugar = Compose . fmap desugar . desugar

instance Sugar []
instance Sugar Maybe
