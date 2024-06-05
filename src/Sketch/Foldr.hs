{- |
Module      : Sketch.Foldr
Copyright   : (c) Niek Mulleners 2024
Maintainer  : n.mulleners@uu.nl

Sketching with 'Data.List.foldr'.

See Figure 5 of "Example-Based Reason About the Realizability of Polymorphic Programs".

-}
module Sketch.Foldr where

import Control.Monad
import Control.Monad.Fresh

import Data.SBV hiding (output)
import Data.SBV.Container
import Data.List.NonEmpty.Utils qualified as NonEmpty

import Base
import Data.Container
import Data.Mono

-- | A functor representing the inputs and outputs of a 'Data.List.foldr'
-- example.
--
-- Use the constructor v'FoldExample' for constructing input-output examples.
--
type FoldExample c f g = Product (Product c (Compose [] f)) g

-- | A constructor for 'Data.List.foldr' examples.
--
-- @
-- v'FoldExample' ctx xs y
-- @
--
-- corresponds to the constraint
--
-- @
-- 'Data.List.foldr' (p ctx) (e ctx) xs == y
-- @
--
-- where
--
-- @
-- p :: forall a. c a -> f a -> g a -> g a
-- e :: forall a. c a -> g a
-- @
--
{-# COMPLETE FoldExample #-}
pattern FoldExample :: c a -> [f a] -> g a -> FoldExample c f g a
pattern FoldExample c f g = Pair (Pair c (Compose f)) g

-- | A set of examples for 'Data.List.foldr'. Each example may have a different
-- monomorphic instantiation.
data FoldExamples = forall c f g. (Container c, Container f, Container g) =>
  FoldExamples [Mono SymVal (FoldExample c f g)]

-- | Compute the constraint for a @foldr@ sketch.
--
-- This is a slight generalization of Figure 5 of "Example-Based Reasoning
-- About the Realizability of Programs", introducing a context parameter.
--
foldr :: FoldExamples -> ConstraintSet
foldr (FoldExamples examples) = runFresh do

  -- Create a symbolic morphism (a hole) for both arguments.
  f <- symMorphism
  e <- symMorphism

  -- Each top-level example is encoded separately.
  forM_ examples
    \(Mono (FoldExample ctx inputs output)) -> do

    -- Create a symbolic container constrained to each input. The inputs are
    -- reversed because foldr goes through a list from right to left.
    xs <- forM (reverse inputs) \i -> do
      x <- symContainer
      constrainExtension x i
      return x

    -- Create a free symbolic container for each intermediate value.
    ys <- replicateM (length inputs) symContainer

    -- Create a symbolic container constrained to the output.
    yn <- symContainer
    constrainExtension yn output

    -- Create a symbolic container constrained to the context argument.
    c <- symContainer
    constrainExtension c ctx

    let y0 :| ys' = NonEmpty.snoc ys yn

    -- The first (intermediate) result is equal to the base case.
    constrainMorphism e c y0

    -- The morphism f is constrained so that each pair of input x_i and
    -- (intermediate) output y_i (along with the context) is mapped to the
    -- next (intermediate) output y_i+1.
    forM_ (zip3 xs ys ys') \(x, y, y') -> do
      constrainMorphism f (pair c (pair x y)) y'
