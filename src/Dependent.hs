{-# LANGUAGE UndecidableInstances #-}

module Dependent (module Dependent) where

import Data.Void

import Data.Kind
import Data.Bifunctor
import Data.Proxy

import Numeric.Natural

import Data.SBV
import Data.SBV.Tuple qualified as SBV
import Data.SBV.Either qualified as SBV

-- | Dependent Types

-- || Raw types

class HasRaw a where
  type Raw a :: Type
  raw :: a -> Raw a

instance Enum a => HasRaw (Bound a) where
  type Raw (Bound a) = Integer
  raw = toInteger . fromEnum

deriving via Bound ()      instance HasRaw ()
deriving via Bound Bool    instance HasRaw Bool
deriving via Bound Int     instance HasRaw Int
deriving via Bound Natural instance HasRaw Natural
deriving via Bound Char    instance HasRaw Char

instance HasRaw Void where
  type Raw Void = Integer
  raw = absurd

instance (HasRaw a, HasRaw b) => HasRaw (a, b) where
  type Raw (a, b) = (Raw a, Raw b)
  raw = bimap raw raw

instance (HasRaw a, HasRaw b) => HasRaw (Either a b) where
  type Raw (Either a b) = Either (Raw a) (Raw b)
  raw = bimap raw raw

-- || Refinement types

class (HasRaw a, SymVal (Raw a)) => Ref a where
  ref :: Proxy a -> SBV (Raw a) -> SBool

newtype Bound a = Bound a
  deriving newtype (Enum)

instance (Enum a, Bounded a) => Ref (Bound a) where
  ref Proxy n = n .>= minVal .&& n .<= maxVal
    where
      minVal = fromIntegral $ fromEnum (minBound :: a)
      maxVal = fromIntegral $ fromEnum (maxBound :: a)

deriving via Bound ()   instance Ref ()
deriving via Bound Bool instance Ref Bool
deriving via Bound Int  instance Ref Int
deriving via Bound Char instance Ref Char

instance Ref Void where
  ref Proxy _ = sFalse

instance Ref Natural where
  ref Proxy n = n .>= 0

instance (Ref a, Ref b) => Ref (a, b) where
  ref Proxy s = let (x, y) = SBV.untuple s in
    ref @a Proxy x .&& ref @b Proxy y

instance (Ref a, Ref b) => Ref (Either a b) where
  ref Proxy = SBV.either (ref @a Proxy) (ref @b Proxy)

-- || Dependent types

class (HasRaw a, Ref (Arg a), SymVal (Raw a)) => Dep a where
  type Arg a :: Type
  dep :: Proxy a -> SBV (Raw (Arg a)) -> SBV (Raw a) -> SBool

newtype K k a = K { unK :: a }
  deriving newtype (Show, Eq, Ord, Enum, Num, HasRaw)

instance (Ref k, Ref a) => Dep (K k a) where
  type Arg (K k a) = k
  dep Proxy _ = ref @a Proxy

newtype Fin = Fin { unFin :: Natural }
  deriving newtype (Eq, Ord, Enum, Num, HasRaw)

instance Dep Fin where
  type Arg Fin = Natural
  dep Proxy n x = x .>= 0 .&& x .< n

data May = May
  deriving stock (Eq, Ord, Show, Enum)
  deriving HasRaw via Bound May

instance Dep May where
  type Arg May = Bool
  dep Proxy m x = m .== 1 .&& x .== 0

newtype OR a b = OR { unOR :: Either a b }
  deriving newtype (Eq, Ord, HasRaw)

instance (Dep a, Dep b) => (Dep (OR a b)) where
  type Arg (OR a b) = (Arg a, Arg b)
  dep Proxy t = let (x, y) = SBV.untuple t in
   SBV.either (dep @a Proxy x) (dep @b Proxy y)

newtype XOR a b = XOR { unXOR :: Either a b }
  deriving newtype (Eq, Ord, HasRaw)

instance (Dep a, Dep b) => (Dep (XOR a b)) where
  type Arg (XOR a b) = Either (Arg a) (Arg b)
  dep Proxy e d = SBV.either
    (\l -> SBV.either (dep @a Proxy l) (const sFalse) d)
    (\r -> SBV.either (const sFalse) (dep @b Proxy r) d)
    e

-- Tests

-- TODO: can we test HasRaw, Ref, and Dep for correctness?
-- 
-- - We can test that values returned by "ref . raw" evaluate to True. (see testRef)
-- - We can test that an arbitrary raw value x evaluates to True only if there
-- exists a value y such that `raw y == x`? A bit difficult to check...
-- - Should we add unraw to HasRaw and check the inverse?
-- - Is there any way to test Dep?? I guess Dep has no laws
--

-- TODO: This should return Prop or Laws, and perhaps use ShowType or smth
refLaws :: forall a. Ref a => a -> Bool
refLaws x = case unliteral (ref (Proxy @a) $ literal $ raw x) of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
