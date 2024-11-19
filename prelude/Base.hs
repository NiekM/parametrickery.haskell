module Base
  ( module Data.Function
  , module Data.Int
  , module Data.String
  , module Data.Void
  , module Data.Bool
  , module Data.Text
  , module Data.Map
  , module Data.Set
  , module Data.Maybe
  , module Data.List
  , module Data.List.NonEmpty
  , module Data.Tuple
  , module Data.Either
  , module Data.Eq
  , module Data.Ord
  , module Data.Enum
  , module Data.Semigroup
  , module Data.Monoid
  , module Data.Functor
  , module Data.Bifunctor
  , module Data.Foldable
  , module Data.Traversable
  , module Data.Type.Equality
  , module Control.Applicative
  , module Control.Monad
  , module Control.Effect.Error
  , module Control.Effect.NonDet
  , module Control.Effect.Reader
  , module Control.Effect.State
  , module Control.Effect.Throw
  , module System.IO
  , module Prettyprinter
  , module Data.Name
  , module GHC.Num
  , module GHC.Show
  , module GHC.Read
  , module GHC.Real
  , Nat
  , Project(..)
  , undefined
  , error
  , trace
  ) where

import Data.Function
  
import GHC.Num (Num(..))
import GHC.Show (Show(..))
import GHC.Read (Read(..))
import GHC.Real (fromIntegral)

import Data.Int (Int)
import Data.String (String)
import Data.Void
import Data.Text (Text)
import Data.Bool
import Data.Map (Map)
import Data.Set (Set)
import Data.Maybe hiding (fromJust)
import Data.List
  ( (++), zip, zipWith, repeat, replicate
  , map, filter, concat, concatMap, reverse)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tuple hiding (Solo)
import Data.Either

import Data.Eq
import Data.Ord
import Data.Enum
import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(..), Sum(..))
import Data.Functor ((<&>), unzip)
import Data.Bifunctor (bimap, first, second)
import Data.Foldable (Foldable(..), and, or, any, all, elem, notElem)
import Data.Traversable (Traversable(..))

import Data.Type.Equality (type (~))

import Control.Applicative
import Control.Monad

import Control.Effect.Error
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Throw

import System.IO

import Prettyprinter (Pretty(..), (<+>), parens, indent)

import Data.Name

import Data.String
import Numeric.Natural (Natural)
import Debug.Trace qualified as Debug
import GHC.Err qualified as Err

undefined :: a
undefined = Err.undefined

error :: String -> a
error = Err.error

trace :: String -> a -> a
trace = Debug.trace

type Nat = Natural

class Project a where
  projections :: a -> [a]
