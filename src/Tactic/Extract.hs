module Tactic.Extract where

import Tactic.Core
import Tactic.Constructors
import Tactic.Elim
import Tactic.Relation

greedyStep :: Tactic sig m => m Filling
greedyStep = anywhere assume <| constructors <| anywhere elim <| anywhere2 relations

extract :: Tactic sig m => m Filling
extract = repeat greedyStep
