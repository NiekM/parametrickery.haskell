{-# LANGUAGE DefaultSignatures #-}

module Data.SBV.Refine
  ( module Data.SBV.Encode
  , Ref(..)
  , refHolds
  ) where

import Data.SBV
import Data.SBV.Tuple qualified as SBV
import Data.SBV.Either qualified as SBV
import Data.SBV.Maybe qualified as SBV

import Data.SBV.Encode

import Base

class Encode a => Ref a where
  ref :: Proxy a -> SBV (Sym a) -> SBool

  default ref :: (a ~ Sym a) => Proxy a -> SBV (Sym a) -> SBool
  ref _ _ = sTrue

instance Ref ()
instance Ref Char
instance Ref Bool
instance Ref Int where
  ref Proxy _ = sTrue

instance Ref Void where
  ref Proxy _ = sFalse

instance Ref Natural where
  ref Proxy n = n .>= 0

instance (Ref a, Ref b) => Ref (a, b) where
  ref Proxy s = let (x, y) = SBV.untuple s in
    ref @a Proxy x .&& ref @b Proxy y

instance (Ref a, Ref b) => Ref (Either a b) where
  ref Proxy = SBV.either (ref @a Proxy) (ref @b Proxy)

instance Ref a => Ref (Maybe a) where
  ref Proxy x = SBV.maybe sTrue (ref @a Proxy) x

-- | Properties

-- TODO: This should return Prop or Laws, and perhaps use ShowType or smth
refHolds :: forall a. Ref a => a -> Bool
refHolds x = case unliteral (ref (Proxy @a) $ literal $ encode x) of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
