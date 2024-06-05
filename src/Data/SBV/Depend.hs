{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
Module      : Data.SBV.Depend
Copyright   : (c) Anonymous 2024
Maintainer  : Anonymous

Dependent types using symbolic representations.

-}
module Data.SBV.Depend
  ( module Data.SBV.Encode
  , module Data.SBV.Refine
  , Dep(..)
  ) where

import Data.SBV

import Data.SBV.Encode
import Data.SBV.Refine

import Base

-- | The class 'Dep' defines a dependent type, by describing how the symbolic
-- encoding is constrained using 'depend' based on its 'Arg'ument.

-- TODO: rewrite using RequiredTypeArguments i.o. AllowAmbiguousTypes
class (Encode a, Ref (Arg a)) => Dep a where
  type Arg a :: Type
  depend :: SBV (Sym (Arg a)) -> SBV (Sym a) -> SBool

instance (Ref a, Ref b) => Dep (Const a b) where
  type Arg (Const a b) = b
  depend _ = refine @a