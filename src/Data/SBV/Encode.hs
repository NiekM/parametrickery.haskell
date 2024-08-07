{- |
Module      : Data.SBV.Encode
Copyright   : (c) Niek Mulleners 2024
Maintainer  : Niek Mulleners

Encoding Haskell values in SBV, for the purpose of modeling
'Data.SBV.Refine.Ref'inement types and 'Data.SBV.Depend.Dep'endent types.

-}
module Data.SBV.Encode where

import Data.Bifunctor
import Data.Int (Int64)

import Data.SBV (SymVal)

import Base

-- | The class 'Encode' describes how a value can be encoded into a symbolic
-- representation.
class SymVal (Sym a) => Encode a where
  type Sym a :: Type
  encode :: a -> Sym a

  type Sym a = a
  default encode :: (Sym a ~ a) => a -> Sym a
  encode = id

instance Encode ()
instance Encode Bool
instance Encode Char
instance Encode Int where
  type Sym Int = Int64
  encode = fromIntegral

-- NOTE: for some reason using Word64 breaks `shiftl`
instance Encode Natural where
  type Sym Natural = Int64
  encode = fromIntegral

instance Encode Void where
  type Sym Void = ()
  encode = absurd

instance (Encode a, Encode b) => Encode (a, b) where
  type Sym (a, b) = (Sym a, Sym b)
  encode = bimap encode encode

instance (Encode a, Encode b) => Encode (Either a b) where
  type Sym (Either a b) = Either (Sym a) (Sym b)
  encode = bimap encode encode

instance Encode a => Encode (Maybe a) where
  type Sym (Maybe a) = Maybe (Sym a)
  encode = fmap encode

instance Encode k => Encode (Const k c) where
  type Sym (Const k c) = Sym k
  encode (Const k) = encode k
