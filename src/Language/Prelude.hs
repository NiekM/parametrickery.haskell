module Language.Prelude (datatypes) where

import GHC.Generics
import Data.Proxy

import Data.Tree

import Language.Generics
import Language.Type

data Nat
  = Zero
  | Succ Nat
  deriving (Eq, Ord, Show, Generic)

-- TODO: define recursive types using fixpoints?
datatypes :: Context
datatypes = Context
  [ toData $ Proxy @Bool
  , toData $ Proxy @Ordering
  , toData $ Proxy @Nat
  , toData $ Proxy @Maybe
  , toData $ Proxy @[]
  , toData $ Proxy @Either
  , toData $ Proxy @Tree
  ]
