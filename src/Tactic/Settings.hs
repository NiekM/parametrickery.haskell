module Tactic.Settings (RealizabilityLevel(..), Settings(..), defaultSettings) where

import Base

data RealizabilityLevel
  = NoRealizability
  | MonoRealizability
  | PolyRealizability
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

data Settings = Settings
  { removeDuplicates   :: Bool
  , removeIrrelevant   :: Bool
  , checkCoverage      :: Bool
  , reconstructProblem :: Bool
  , realizabilityLevel :: RealizabilityLevel
  } deriving stock (Eq, Ord, Show, Read)

defaultSettings :: Settings
defaultSettings = Settings
  { removeDuplicates   = True
  , removeIrrelevant   = False
  , checkCoverage      = True
  , reconstructProblem = True
  , realizabilityLevel = PolyRealizability
  }
