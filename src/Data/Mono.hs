{-# LANGUAGE TypeAbstractions#-}

module Data.Mono where

-- TODO: Find a better name

import Base

data Mono (c :: Type -> Constraint) f where
  Mono :: forall a c f. c a => f a -> Mono c f

mapMono :: (forall a. c a => f a -> g a) -> Mono c f -> Mono c g
mapMono f (Mono @a x) = Mono @a (f x)
