module Base
  ( module Data.Function
  , module Data.Functor
  , module Data.Bifunctor
  , module Data.Void
  , module Data.Ord
  , module Data.Text
  , module Data.Map
  , module Data.Set
  , module Data.Maybe
  , module Data.List.NonEmpty
  , module Data.Tuple
  , module Data.Either
  , module Control.Monad
  , module Control.Effect.Throw
  , module Control.Effect.Reader
  , module Control.Effect.State
  , module Control.Effect.NonDet
  , module Prettyprinter
  , Nat
  ) where

import Data.Function ((&), on)
import Data.Functor ((<&>))
import Data.Bifunctor (bimap, first, second)
  
import Data.Void
import Data.Ord
import Numeric.Natural (Natural)
import Data.Text (Text)

import Data.Map (Map)
import Data.Set (Set)
import Data.Maybe (fromMaybe, mapMaybe, isJust, isNothing)
import Data.List.NonEmpty (NonEmpty(..))

import Data.Tuple (swap)
import Data.Either (partitionEithers)

import Control.Monad

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.NonDet

import Prettyprinter

type Nat = Natural
