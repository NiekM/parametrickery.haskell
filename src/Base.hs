module Base
  ( module GHC.TypeLits
  , module Data.Kind
  , module Data.Function
  , module Data.Functor
  , module Data.Bifunctor
  , module Data.Void
  , module Data.Coerce
  , module Data.Proxy
  , module Data.Text
  , module Data.Map
  , module Data.Set
  , module Data.Maybe
  , module Data.List
  , module Data.List.NonEmpty
  , module Control.Monad
  , module Prettyprinter
  , Nat
  ) where

import GHC.TypeLits (Symbol)

import Data.Kind (Type, Constraint)
import Data.Function ((&), on)
import Data.Functor ((<&>))
import Data.Bifunctor (bimap, first, second)
  
import Data.Void
import Data.Coerce (coerce)
import Data.Proxy

import Numeric.Natural (Natural)
import Data.Text (Text)

import Data.Map (Map)
import Data.Set (Set)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (transpose)
import Data.List.NonEmpty (NonEmpty(..))

import Control.Monad (join, (>=>), forM)

import Prettyprinter

type Nat = Natural