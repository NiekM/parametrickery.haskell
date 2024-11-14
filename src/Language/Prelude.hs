module Language.Prelude (datatypes) where

import GHC.Generics

import Data.Maybe
import Data.Tree.Binary

import Language.Generics
import Language.Type

data Nat
  = Zero
  | Succ Nat
  deriving (Eq, Ord, Show, Generic)

data Some a = Cons a (Maybe (Some a))
  deriving (Eq, Ord, Show, Generic)

-- TODO: define recursive types using fixpoints?
datatypes :: Context
datatypes = Context $
  [ toData Bool
  , toData Ordering
  , toData Nat
  , toData Maybe
  , toData (type [])
  , toData Either
  , toData Tree
  , toData Some
  ] >>= \d -> d : maybeToList (base d)
