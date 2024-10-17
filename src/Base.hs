module Base
  ( module Data.Function
  , module Data.Functor
  , module Data.Bifunctor
  , module Data.Void
  , module Data.Ord
  , module Data.Text
  , module Data.Monoid
  , module Data.Map
  , module Data.Set
  , module Data.Maybe
  , module Data.List.NonEmpty
  , module Data.Tuple
  , module Data.Either
  , module Control.Monad
  , module Control.Effect.Error
  , module Control.Effect.NonDet
  , module Control.Effect.Reader
  , module Control.Effect.State
  , module Control.Effect.Throw
  , module Prettyprinter
  , module Data.Name
  , Nat
  ) where

import Data.Function ((&), on)
import Data.Functor ((<&>))
import Data.Bifunctor (bimap, first, second)
  
import Data.Void
import Data.Ord
import Numeric.Natural (Natural)
import Data.Text (Text)

import Data.Monoid (Sum(..))
import Data.Map (Map)
import Data.Set (Set)
import Data.Maybe (fromMaybe, mapMaybe, isJust, isNothing)
import Data.List.NonEmpty (NonEmpty(..))

import Data.Tuple (swap)
import Data.Either (partitionEithers)

import Control.Monad

import Control.Effect.Error
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Throw

import Prettyprinter (Pretty(..), (<+>), parens)

import Data.Name

type Nat = Natural
