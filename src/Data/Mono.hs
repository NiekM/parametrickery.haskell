{-# LANGUAGE TypeAbstractions #-}

{- |
Module      : Data.Mono
Copyright   : (c) Anonymous 2024
Maintainer  : Anonymous

Monomorphic instantiations of Functors.

-}
module Data.Mono where

import Base

-- | A wrapper over a functor @f@, instantiating it with an existential
-- monomorphic type constrained by @c@.
data Mono (c :: Type -> Constraint) (f :: Type -> Type) where
  Mono :: forall a c f. c a => f a -> Mono c f

-- | Map a function over the content of a t'Mono', possibly changing the
-- underlying functor.
mapMono :: (forall a. c a => f a -> g a) -> Mono c f -> Mono c g
mapMono f (Mono @a x) = Mono @a (f x)
