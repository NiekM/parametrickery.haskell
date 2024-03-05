module Base
  ( module Data.Kind
  , module Data.Function
  , module Data.Functor
  , module Identity
  , module Const
  , module Sum
  , module Product
  , module Compose
  , module Data.Void
  , module Data.Coerce
  , module Data.Proxy
  , module Numeric.Natural
  , module Data.Map
  )
  where

import Data.Kind (Type, Constraint)
import Data.Function ((&))
import Data.Functor ((<&>))
  
import Data.Functor.Identity as Identity (Identity(..))
import Data.Functor.Const    as Const    (Const   (..))
import Data.Functor.Sum      as Sum      (Sum     (..))
import Data.Functor.Product  as Product  (Product (..))
import Data.Functor.Compose  as Compose  (Compose (..))

import Data.Void
import Data.Coerce (coerce)
import Data.Proxy

import Numeric.Natural (Natural)

import Data.Map (Map)
