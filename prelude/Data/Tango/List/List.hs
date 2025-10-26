module Data.Tango.List.List where

import Base
import GHC.Generics

data TangoListList a b = NN | CN a [a] | NC b [b] | CC a b (TangoListList a b)
  deriving (Eq, Ord, Show, Generic)

tango :: [a] -> [b] -> TangoListList a b
tango [] [] = NN
tango (x:xs) [] = CN x xs
tango [] (y:ys) = NC y ys
tango (x:xs) (y:ys) = CC x y (tango xs ys)

data TangoListListF a b r = NNF | CNF a [a] | NCF b [b] | CCF a b r

foldTango :: (TangoListListF a b r -> r) -> TangoListList a b -> r
foldTango alg = \case
  NN -> alg NNF
  CN x xs -> alg $ CNF x xs
  NC y ys -> alg $ NCF y ys
  CC x y xys -> alg $ CCF x y (foldTango alg xys)
