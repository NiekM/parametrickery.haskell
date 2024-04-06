module Base
  ( module GHC.TypeLits
  , module Data.Kind
  , module Data.Function
  , module Data.Functor
  , module Data.Bifunctor
  , module Identity
  , module Const
  , module Sum
  , module Product
  , module Compose
  , module Classes
  , module Data.Void
  , module Data.Coerce
  , module Data.Proxy
  , module Numeric.Natural
  , module Data.Map
  , module Data.Set
  , module Data.Maybe
  , module Data.List
  , module Data.List.NonEmpty
  ) where

import GHC.TypeLits (Symbol)

import Data.Kind (Type, Constraint)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Bifunctor (first, second)
  
import Data.Functor.Identity as Identity (Identity(..))
import Data.Functor.Const    as Const    (Const   (..))
import Data.Functor.Sum      as Sum      (Sum     (..))
import Data.Functor.Product  as Product  (Product (..))
import Data.Functor.Compose  as Compose  (Compose (..))

import Data.Functor.Classes as Classes

import Data.Void
import Data.Coerce (coerce)
import Data.Proxy

import Numeric.Natural (Natural)

import Data.Map (Map)
import Data.Set (Set)
import Data.Maybe (fromMaybe)
import Data.List (transpose)
import Data.List.NonEmpty (NonEmpty(..))
