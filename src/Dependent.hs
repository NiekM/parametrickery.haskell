module Dependent
  ( module Dependent
  , module Data.SBV.Encode
  , module Data.SBV.Refine
  , module Data.SBV.Depend
  ) where

import Data.SBV

import Data.SBV.Encode
import Data.SBV.Refine
import Data.SBV.Depend

import Base

-- Tests

-- TODO: This should return Prop or Laws, and perhaps use ShowType or smth
refHolds :: forall a. Ref a => a -> Bool
refHolds x = case unliteral (ref (Proxy @a) $ literal $ encode x) of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b

depHolds :: forall a. Dep a => (Arg a) -> a -> Bool
depHolds x y = case unliteral (dep (Proxy @a) x' y') of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
  where
    x' = literal (encode x)
    y' = literal (encode y)

-- TODO: This should return Prop or Laws, and perhaps use ShowType or smth
refLaws :: forall a. Ref a => a -> Bool
refLaws = refHolds

instance Ref k => Dep (Const k ()) where
  type Arg (Const k ()) = ()
  dep Proxy _ y = ref @k Proxy y
