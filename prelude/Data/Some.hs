module Data.Some where

import Base
import GHC.Generics

data Some a = Cons a (Maybe (Some a))
  deriving (Eq, Ord, Show, Generic)

toSome :: a -> [a] -> Some a
toSome x [] = Cons x Nothing
toSome x (y:ys) = Cons x . Just $ toSome y ys
