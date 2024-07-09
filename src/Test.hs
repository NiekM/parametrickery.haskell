{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test where

import Control.Applicative (Alternative)
import Data.Coerce (coerce)
import Data.Either (isRight)
import Data.Foldable (asum)
import Data.Monoid (Alt(..))
import Data.Maybe (fromJust)
import Data.Text.IO qualified as Text
import System.IO.Unsafe qualified as Unsafe

import Base
import Data.Map.Multi qualified as Multi
import Data.Named
import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Declaration
import Language.Parser
import Refinements

-- ToExpr is no longer really necessary now that we have parsing, but it's still
-- useful sometimes.
class    ToExpr a    where toVal :: a -> Expr h
instance ToExpr Int  where toVal = Lit . MkInt
instance ToExpr Bool where toVal = Lit . MkBool
instance ToExpr ()   where toVal = const Unit

instance ToExpr a => ToExpr [a] where
  toVal = Lst . map toVal

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
  toVal = uncurry Pair . bimap toVal toVal

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
  toVal = either Inl Inr . bimap toVal toVal

------ Examples ------

loadProblem :: String -> Problem
loadProblem file = Unsafe.unsafePerformIO do
  t <- Text.readFile $ "data/examples/" <> file
  return . value $ parse t

parse :: Parse a => Text -> a
parse = fromJust . lexParse parser

triple :: Problem
triple = loadProblem "triple"

-- >>> pretty <$> check triple
-- PositionConflict

constant :: Problem
constant = loadProblem "constant"

pairExample :: Problem
pairExample = loadProblem "pair"

-- >>> pretty $ check pairExample
-- _ : forall a b. {x : a, y : b} -> a * b
-- _ a0 b0 = (a0, b0)

introPairExample :: [[Problem]]
introPairExample = introPair pairExample

-- >>> pretty introPairExample
-- [ [ _ : forall a b. {x : a, y : b} -> a
--   _ 1 True = 1
--   _ False 3 = False
--   , _ : forall a b. {x : a, y : b} -> b
--   _ 1 True = True
--   _ False 3 = 3 ] ]

zipExample :: Problem
zipExample = loadProblem "zip"

lenExample :: Problem
lenExample = loadProblem "len"

tailExample :: Problem
tailExample = loadProblem "tail"

sortExample :: Problem
sortExample = loadProblem "sort"

twoRelations :: Problem
twoRelations = parse
  "_ : forall a b. (Ord a, Eq b) => {xs : [a * b]} -> [a] * [b]\n\
  \_ [(1, 2), (3, 4)] = ([1, 3], [2, 4])\n\
  \_ [(1, 2)] = ([1], [2])\n\
  \_ [(1, 2), (1, 2), (1, 2)] = ([1], [2])"

isFold :: Problem -> [Result [PolyProblem]]
isFold p = introFoldr p <&> traverse check

-- New functions


-- TODO: check if this behaves as expected
-- It is a bit random that this one works on Containers and applyExamples works
-- on Terms.
applyExample :: [Relation] -> [Container] -> PolyExample -> Maybe Container
applyExample rels inputs PolyExample { relations, inShapes, outShape, origins }
  | inShapes == map shape inputs
  , relations == rels
  , Just outPos <- outPositions = Just Container
    { shape = outShape
    , positions = outPos
    }
  | otherwise = Nothing
  where
    inPositions = Multi.fromMap $ foldMap positions inputs
    outPositions = Multi.toMap $ Multi.compose inPositions origins

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

applyPoly :: [Container] -> PolyProblem -> Maybe Container
applyPoly containers Declaration { signature, bindings } =
  altMap (applyExample relations containers) bindings
    where
      p = foldMap positions containers
      relations = computeRelations (constraints signature) p
