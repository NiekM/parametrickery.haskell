{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test where

import Control.Applicative (Alternative)
import Data.Coerce (coerce)
import Data.Either (isRight)
import Data.Foldable (asum)
import Data.List qualified as List
import Data.Monoid (Alt(..))
import Data.Maybe (fromJust)
import Data.Text.IO qualified as Text
import Prettyprinter
import System.IO.Unsafe qualified as Unsafe
import System.Directory

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
instance ToExpr ()   where toVal = const $ Tuple []

instance ToExpr a => ToExpr [a] where
  toVal = Lst . map toVal

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
  toVal (x, y) = Tuple [toVal x, toVal y]

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
  toVal = either (Proj 0 2) (Proj 1 2) . bimap toVal toVal

------ Utilities ------

parse :: Parse a => Text -> a
parse = fromJust . lexParse parser

inspect :: (Show a, Pretty a) => a -> IO ()
inspect x = do
  print x
  putStrLn ""
  print (pretty x)

instance (Pretty e, Pretty a) => Pretty (Either e a) where
  pretty = either pretty pretty

------ Examples -------

{-# NOINLINE bench #-}
bench :: [Named Problem]
bench = Unsafe.unsafePerformIO do
  xs <- listDirectory "data/bench/"
  forM (reverse xs) \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    return $ parse content

getBench :: Text -> Problem
getBench name = maybe (error "unknown benchmark") (.value) $
  bench & List.find \problem -> problem.name == name

-- triple :: Problem
-- triple = loadProblem "triple"

-- >>> pretty <$> check triple
-- PositionConflict

-- constant :: Problem
-- constant = loadProblem "constant"

-- pairExample :: Problem
-- pairExample = loadProblem "pair"

-- >>> pretty $ check pairExample
-- _ : {x : a, y : b} -> (a, b)
-- _ a0 b0 = (a0, b0)

-- introPairExample :: DisCon Problem
-- introPairExample = introTuple pairExample

-- >>> pretty introPairExample
-- [ [ _ : forall a b. {x : a, y : b} -> a
--   _ 1 True = 1
--   _ False 3 = False
--   , _ : forall a b. {x : a, y : b} -> b
--   _ 1 True = True
--   _ False 3 = 3 ] ]

revExample :: Problem
revExample = getBench "reverse"

zipExample :: Problem
zipExample = getBench "zip"

lenExample :: Problem
lenExample = getBench "length"

tailExample :: Problem
tailExample = getBench "length"

nubExample :: Problem
nubExample = getBench "nub"

sortExample :: Problem
sortExample = getBench "sort"

-- TODO: can we figure out that in the recursive call, the left list is only
-- relevant for the left output and the right list only relevant for the right
-- output?
pivot :: Problem
pivot = getBench "pivot"

swapExample :: Problem
swapExample = getBench "swap"

append :: Problem
append = getBench "append"

twoRelations :: Problem
twoRelations = parse
  "_ : forall a b. (Ord a, Eq b) => {xs : [(a, b)]} -> ([a], [b])\n\
  \_ [(1, 2), (3, 4)] = ([1, 3], [2, 4])\n\
  \_ [(1, 2)] = ([1], [2])\n\
  \_ [(1, 2), (1, 2), (1, 2)] = ([1], [2])"

isFold :: Named Problem -> [Either Conflict [Named PolyProblem]]
isFold (Named name p) = traverse (fmap (Named name) . check) <$> xs
  where DisCon xs = introFoldr p

-- New functions

-- TODO: check if this behaves as expected
-- It is a bit random that this one works on Containers and applyExamples works
-- on Terms.
applyExample :: [Relation] -> [Container] -> PolyExample -> Maybe Container
applyExample rels inputs PolyExample { relations, inShapes, outShape, origins }
  | inShapes == map (.shape) inputs
  , relations == rels
  , Just outPos <- outPositions = Just Container
    { shape = outShape
    , elements = outPos
    }
  | otherwise = Nothing
  where
    inPositions = Multi.fromMap $ foldMap (.elements) inputs
    outPositions = Multi.toMap $ Multi.compose inPositions origins

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

applyPoly :: [Container] -> PolyProblem -> Maybe Container
applyPoly containers Declaration { signature, bindings } =
  altMap (applyExample relations containers) bindings
    where
      elements = foldMap (.elements) containers
      relations = computeRelations signature.constraints elements
