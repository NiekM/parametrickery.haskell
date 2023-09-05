module Types (module Types) where

import Numeric.Natural

newtype Fin = Fin Natural
  deriving newtype (Eq, Ord, Read, Show, Enum, Num)

-- We could also just use Identity, does that make sense?
newtype K a = K { runK :: a }
  deriving newtype (Eq, Ord, Read, Show)