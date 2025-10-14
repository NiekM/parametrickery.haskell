{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# LANGUAGE OverloadedLists #-}
-- It takes two!
module Tango where

import Base
import GHC.Exts

newtype Fix f = Fix { unFix :: f (Fix f) }

data NatF r = S r | Z

instance Num (Fix NatF) where
  fromInteger = fixNat . fromInteger

instance Show (Fix NatF) where
  show = show . unFixNat

fixNat :: Nat -> Fix NatF
fixNat 0 = Fix Z
fixNat n = Fix (S $ fixNat (n - 1))

unFixNat :: Fix NatF -> Nat
unFixNat (Fix Z) = 0
unFixNat (Fix (S n)) = 1 + unFixNat n

data ListF a r = C a r | N

instance IsList (Fix (ListF a)) where
  type Item (Fix (ListF a)) = a
  fromList = fixList
  toList = unFixList

instance Show a => Show (Fix (ListF a)) where
  show = show . unFixList

fixList :: [a] -> Fix (ListF a)
fixList [] = Fix N
fixList (x:xs) = Fix (C x $ fixList xs)

unFixList :: Fix (ListF a) -> [a]
unFixList (Fix N) = []
unFixList (Fix (C x xs)) = x : unFixList xs

-- TODO: can we automatically generate such Tango functors?
data TangoListList a b r = NN | CN a (Fix (ListF a)) | NC b (Fix (ListF b)) | CC a b r

tango :: (TangoListList a b c -> c) -> Fix (ListF a) -> Fix (ListF b) -> c
tango alg (Fix N) (Fix N) = alg NN
tango alg (Fix (C x xs)) (Fix N) = alg $ CN x xs
tango alg (Fix N) (Fix (C y ys)) = alg $ NC y ys
tango alg (Fix (C x xs)) (Fix (C y ys)) = alg $ CC x y (tango alg xs ys)

zip :: Fix (ListF a) -> Fix (ListF b) -> Fix (ListF (a, b))
zip = tango \case
  CC x y r -> Fix $ C (x, y) r
  _ -> Fix N

longZip :: Monoid a => Fix (ListF a) -> Fix (ListF a) -> Fix (ListF a)
longZip = tango \case
  NN -> Fix N
  CN x xs -> Fix $ C x xs
  NC y ys -> Fix $ C y ys
  CC x y r -> Fix $ C (x <> y) r

data TangoListNat a r = NZ | CZ a (Fix (ListF a)) | NS (Fix NatF) | CS a r

tangoN :: (TangoListNat a c -> c) -> Fix (ListF a) -> Fix NatF -> c
tangoN alg (Fix N) (Fix Z) = alg NZ
tangoN alg (Fix (C x xs)) (Fix Z) = alg $ CZ x xs
tangoN alg (Fix N) (Fix (S n)) = alg $ NS n
tangoN alg (Fix (C x xs)) (Fix (S n)) = alg $ CS x (tangoN alg xs n)

take :: Fix (ListF a) -> Fix NatF -> Fix (ListF a)
take = tangoN \case
  CS x r -> Fix (C x r)
  _ -> Fix N

drop :: Fix (ListF a) -> Fix NatF -> Fix (ListF a)
drop = tangoN \case
  CZ x xs -> Fix (C x xs)
  CS _ r -> r
  _ -> Fix N

index :: Fix (ListF a) -> Fix NatF -> Maybe a
index = tangoN \case
  CZ x _ -> Just x
  CS _ r -> r
  _ -> Nothing

splitAt :: Fix (ListF a) -> Fix NatF -> (Fix (ListF a), Fix (ListF a))
splitAt = tangoN \case
  CZ x xs -> ([], Fix (C x xs))
  CS x (xs, ys) -> (Fix (C x xs), ys)
  _ -> ([], [])

data TreeF a r = B r a r | L

data TangoTreeNat a r = LZ | BZ (Fix (TreeF a)) a (Fix (TreeF a)) | LS (Fix NatF) | BS r a r

tangoT :: (TangoTreeNat a c -> c) -> Fix (TreeF a) -> Fix NatF -> c
tangoT alg (Fix L) (Fix Z) = alg LZ
tangoT alg (Fix (B l x r)) (Fix Z) = alg $ BZ l x r
tangoT alg (Fix L) (Fix (S n)) = alg $ LS n
tangoT alg (Fix (B l x r)) (Fix (S n)) = alg $ BS (tangoT alg l n) x (tangoT alg r n)

level :: Fix (TreeF a) -> Fix (NatF) -> [a]
level = tangoT \case
  BZ _ x _ -> [x]
  BS l _ r -> l ++ r
  _ -> []

data TangoNatNat r = ZZ | SZ (Fix NatF) | ZS (Fix NatF) | SS r

tangoNN :: (TangoNatNat c -> c) -> Fix NatF -> Fix NatF -> c
tangoNN alg (Fix Z) (Fix Z) = alg ZZ
tangoNN alg (Fix (S n)) (Fix Z) = alg $ SZ n
tangoNN alg (Fix Z) (Fix (S n)) = alg $ ZS n
tangoNN alg (Fix (S n)) (Fix (S m)) = alg $ SS (tangoNN alg n m)

max :: Fix NatF -> Fix NatF -> Fix NatF
max = tangoNN \case
  ZZ -> Fix Z
  SZ n -> Fix (S n)
  ZS n -> Fix (S n)
  SS n -> Fix (S n)

min :: Fix NatF -> Fix NatF -> Fix NatF
min = tangoNN \case
  SS n -> Fix (S n)
  _ -> Fix Z

compare :: Fix NatF -> Fix NatF -> Ordering
compare = tangoNN \case
  ZZ -> EQ
  SZ _ -> GT
  ZS _ -> LT
  SS r -> r

data SomeF a r = C' a (Maybe r)

makeSome :: a -> [a] -> Fix (SomeF a)
makeSome x xs = Fix $ C' x case xs of
  [] -> Nothing
  y:ys -> Just (makeSome y ys)

data TangoListSome a b r = NC' b (Maybe (Fix (SomeF b))) | CC' a b (Maybe r)

-- TODO: figure out if this works as intended
tangoLS :: (TangoListSome a b c -> c) -> Fix (ListF a) -> Fix (SomeF b) -> c
tangoLS alg (Fix N) (Fix (C' x xs)) = alg $ NC' x xs
tangoLS alg (Fix (C x xs)) (Fix (C' y Nothing)) = alg $ CC' x y Nothing
tangoLS alg (Fix (C x xs)) (Fix (C' y (Just zs))) = alg $ CC' x y (Just $ tangoLS alg xs zs)
-- tangoLS alg (Fix (C x xs)) (Fix (C' y ys)) = alg $ CC' x y do
--   ys' <- ys
--   return $ tangoLS alg xs ys'

data TangoNatSome a r = ZC' a (Maybe (Fix (SomeF a))) | SC' a (Maybe r)

tangoNS :: (TangoNatSome a c -> c) -> Fix NatF -> Fix (SomeF a) -> c
tangoNS alg (Fix Z) (Fix (C' x xs)) = alg $ ZC' x xs
tangoNS alg (Fix (S n)) (Fix (C' x xs)) = alg $ SC' x do
  xs' <- xs
  return $ tangoNS alg n xs'

indexSome :: Fix NatF -> Fix (SomeF a) -> Maybe a
indexSome = tangoNS \case
  ZC' x _ -> Just x
  SC' _ (Just r) -> r
  _ -> Nothing

  
--
-- index :: Fix (ListF a) -> Fix NatF -> Maybe a
-- index = tangoN \case
--   CZ x _ -> Just x
--   CS _ r -> r
--   _ -> Nothing
