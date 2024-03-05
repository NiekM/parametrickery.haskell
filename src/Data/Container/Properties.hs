module Data.Container.Properties
  ( containerRoundTrip
  , containerDependencies
  ) where

import Data.Map qualified as Map

import Data.Container.Core (Extension(..), Container(..))
import Data.SBV.Depend (refHolds, depHolds)

containerRoundTrip :: forall f a. (Container f, Eq (f a)) => f a -> Bool
containerRoundTrip x = x == fromContainer (toContainer x)

containerDependencies :: forall f a. (Container f, Eq (f a)) => f a -> Bool
containerDependencies x = refHolds s && all (depHolds s) (Map.keys p)
  where Extension s p = toContainer x
