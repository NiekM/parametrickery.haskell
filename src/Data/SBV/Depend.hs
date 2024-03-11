{-# LANGUAGE UndecidableInstances #-}

module Data.SBV.Depend
  ( module Data.SBV.Encode
  , module Data.SBV.Refine
  , Dep(..)
  , depHolds
  ) where

import Data.SBV

import Data.SBV.Encode
import Data.SBV.Refine

import Base

class (Encode a, Ref (Arg a)) => Dep a where
  type Arg a :: Type
  dep :: Proxy a -> SBV (Sym (Arg a)) -> SBV (Sym a) -> SBool

instance (Ref a, Ref b) => Dep (Const a b) where
  type Arg (Const a b) = b
  dep Proxy _ y = ref @a Proxy y

-- | Properties

depHolds :: forall a. Dep a => (Arg a) -> a -> Bool
depHolds x y = case unliteral (dep (Proxy @a) x' y') of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
  where
    x' = literal (encode x)
    y' = literal (encode y)
