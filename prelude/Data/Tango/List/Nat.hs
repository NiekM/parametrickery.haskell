module Data.Tango.List.Nat where

import Base
import GHC.Generics

data TangoListNat a = NZ | CZ a [a] | NS Nat | CS a (TangoListNat a)
  deriving (Eq, Ord, Show, Generic)

tango :: [a] -> Nat -> TangoListNat a
tango [] 0 = NZ
tango (x:xs) 0 = CZ x xs
tango [] n = NS (n - 1)
tango (x:xs) n = CS x (tango xs (n - 1))

data TangoListNatF a r = NZF | CZF a [a] | NSF Nat | CSF a r

foldTango :: (TangoListNatF a r -> r) -> TangoListNat a -> r
foldTango alg = \case
  NZ -> alg NZF
  CZ x xs -> alg $ CZF x xs
  NS n -> alg $ NSF n
  CS x xns -> alg $ CSF x (foldTango alg xns)
