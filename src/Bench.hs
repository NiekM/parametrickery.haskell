module Bench where

import Base

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Directory
import Test.QuickCheck (Property, discard)

import Language.Generics (Interpret(..))
import Language.Problem
import Language.Parser
import Language.Expr
import Synth

import Test.Compare
import Bench.Model qualified as Model

trySynthesize :: Arguments -> Problem -> Maybe (Program Void)
trySynthesize args problem = case synthesize args problem of
  Failure Depleted -> Nothing
  Failure Exhausted -> Nothing
  Success ((_, Unfinished _filling) :| _) -> Nothing
  Success ((_, Finished program) :| _)
    | testProblem program problem -> Just program
    | otherwise -> Nothing

testSynthesis :: Arguments -> Problem -> Model -> Property
testSynthesis args problem (Model model) = case trySynthesize args problem of
  Nothing -> discard
  Just program -> comparison model (interpret program)

loadProblem :: Name -> IO Problem
loadProblem name = do
  content <- Text.readFile $ "data/bench/" <> Text.unpack name.getName
  case lexParse (parser @(Named Problem)) content of
    Nothing -> error $ "Failed to parse " <> show (pretty name)
    Just problem -> return problem.value

loadAll :: IO [Named Problem]
loadAll = do
  xs <- listDirectory "data/bench/"
  forM (reverse xs) \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    case lexParse (parser @(Named Problem)) content of
      Nothing -> error $ "Failed to parse " <> show (pretty name)
      Just problem -> return problem


data Model = forall a. (Compare a, Interpret a) => Model a

models :: [Named [Named Model]]
models =
  [ Named "simple"
    [ Named "append"            . Model $ Model.append @Int
    , Named "concat"            . Model $ Model.concat @Int
    , Named "drop"              . Model $ Model.drop @Int
    , Named "head"              . Model $ Model.head @Int
    , Named "index"             . Model $ Model.index @Int
    , Named "init"              . Model $ Model.init @Int
    , Named "last"              . Model $ Model.last @Int
    , Named "length"            . Model $ Model.length @Int
    , Named "null"              . Model $ Model.null @Int
    , Named "prepend"           . Model $ Model.prepend @Int
    , Named "reverse"           . Model $ Model.reverse @Int
    , Named "splitAt"           . Model $ Model.splitAt @Int
    , Named "tail"              . Model $ Model.tail @Int
    , Named "take"              . Model $ Model.take @Int
    , Named "unzip"             . Model $ Model.unzip @Int @Int
    , Named "zip"               . Model $ Model.zip @Int @Int
    ]

  , Named "extra"
    [ Named "cartesian"         . Model $ Model.cartesian @Int
    , Named "copyFirst"         . Model $ Model.copyFirst @Int
    , Named "copyLast"          . Model $ Model.copyLast @Int
    , Named "shiftl"            . Model $ Model.shiftl @Int
    , Named "shiftr"            . Model $ Model.shiftr @Int
    , Named "partition"         . Model $ Model.partition @Int @Int
    ]

  , Named "trees"
    [ Named "breadthFirst"      . Model $ Model.breadthFirst @Int @()
    , Named "depth"             . Model $ Model.depth @Int @()
    , Named "inorder"           . Model $ Model.inorder @Int @()
    , Named "levels"            . Model $ Model.levels @Int @()
    , Named "mirror"            . Model $ Model.mirror @Int @()
    , Named "size"              . Model $ Model.size @Int @()
    ]

  , Named "eq"
    [ Named "compress"          . Model $ Model.compress @Int
    , Named "group"             . Model $ Model.group @Int
    , Named "elem"              . Model $ Model.elem @Int
    , Named "elemIndex"         . Model $ Model.elemIndex @Int
    , Named "nub"               . Model $ Model.nub @Int
    , Named "union"             . Model $ Model.union @Int
    ]

  , Named "ord"
    [ Named "insert"            . Model $ Model.insert @Int
    , Named "maximum"           . Model $ Model.maximum @Int
    , Named "ordNub"            . Model $ Model.ordNub @Int
    , Named "pivot"             . Model $ Model.pivot @Int
    , Named "sort"              . Model $ Model.sort @Int
    , Named "sorted"            . Model $ Model.sorted @Int
    ]
  ]
