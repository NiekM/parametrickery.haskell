-- | Tactics inspired by refinery.
module Tactic
  ( module Tactic.Check
  , module Tactic.Constructors
  , module Tactic.Core
  , module Tactic.Elim
  , module Tactic.Hole
  , module Tactic.Relation
  ) where

import Tactic.Check
import Tactic.Constructors
import Tactic.Core
import Tactic.Elim
import Tactic.Hole
import Tactic.Relation

-- NOTE: some functions do not work well as combinators, such as all and any, since there is no good way to figure out how each input contributed to the result.
