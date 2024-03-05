{-# LANGUAGE UndecidableInstances #-}

module Data.SBV.Depend
  ( module Data.SBV.Encode
  , module Data.SBV.Refine
  , Dep(..)
  , depHolds
  ) where

import Data.SBV
import Data.SBV.Maybe qualified as SBV

import Data.SBV.Encode
import Data.SBV.Refine

import Base

class (Encode a, Ref (Arg a)) => Dep a where
  type Arg a :: Type
  dep :: Proxy a -> SBV (Sym (Arg a)) -> SBV (Sym a) -> SBool

instance Dep Bool where
  type Arg Bool = ()
  dep Proxy _ _ = sTrue

instance Dep a => Dep (Maybe a) where
  type Arg (Maybe a) = Maybe (Arg a)
  dep Proxy x y = SBV.maybe (SBV.isNothing y)
    (\z -> SBV.maybe sFalse (dep @a Proxy z) y) x

-- | Properties

depHolds :: forall a. Dep a => (Arg a) -> a -> Bool
depHolds x y = case unliteral (dep (Proxy @a) x' y') of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
  where
    x' = literal (encode x)
    y' = literal (encode y)
