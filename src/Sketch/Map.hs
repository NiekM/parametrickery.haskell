{- |
Module      : Sketch.Map
Copyright   : (c) Niek Mulleners 2024
Maintainer  : Niek Mulleners

Sketching with 'Data.List.map'.

See Figure 4 of "Example-Based Reason About the Realizability of Polymorphic Programs".

-}
module Sketch.Map where

import Prelude hiding (map)

import Control.Monad
import Control.Monad.Fresh

import Data.SBV hiding (output)
import Data.SBV.Container

import Base
import Data.Container
import Data.Mono

-- | A functor representing the inputs and outputs of a 'Data.List.map' example.
--
-- Use the constructor v'MapExample' for constructing input-output examples.
--
type MapExample c f g = Product (Product c (Compose [] f)) (Compose [] g)

-- | A constructor for 'Data.List.map' examples.
--
-- @
-- v'MapExample' ctx xs ys
-- @
--
-- corresponds to the constraint
--
-- @
-- 'Data.List.map' (p ctx) xs == ys
-- @
--
-- where
--
-- @
-- p :: forall a. c a -> f a -> g a
-- @
--
{-# COMPLETE MapExample #-}
pattern MapExample :: c a -> [f a] -> [g a] -> MapExample c f g a
pattern MapExample c f g = Pair (Pair c (Compose f)) (Compose g)

-- | A set of examples for 'Data.List.map'. Each example may have a different
-- monomorphic instantiation.
data MapExamples = forall c f g. (Container c, Container f, Container g) =>
  MapExamples [Mono SymVal (MapExample c f g)]

-- | Compute the constraint for a 'Data.List.map' sketch.
--
-- This is a slight generalization of Figure 4 of "Example-Based Reasoning
-- About the Realizability of Programs", introducing a context parameter.
--
-- For example, we can show that 'Data.List.reverse' cannot be implemented as a
-- map:
--
-- >>> input  = [1,2,3] :: [Identity Integer]
-- >>> output = [3,2,1] :: [Identity Integer]
-- >>> sat . map $ MapExamples [Mono $ MapExample (Const ()) input output]
-- Unsatisfiable
--
map :: MapExamples -> ConstraintSet
map (MapExamples examples) = runFresh do

  -- Create a symbolic morphism (a hole) for the argument f.
  f <- symMorphism

  -- Each top-level example is encoded separately.
  forM_ examples
    \(Mono (MapExample ctx inputs outputs)) -> do

    -- The input and output lists should have the same length.
    constrain . fromBool $ length inputs == length outputs

    -- Create a symbolic container constrained to the context argument.
    c <- symContainer
    constrainExtension c ctx

    -- Per example, each input-output pair is encoded separately.
    forM_ (zip inputs outputs) \(i, o) -> do

      -- Create a symbolic container constrained to the input.
      x <- symContainer
      constrainExtension x i

      -- Create a symbolic container constrained to the output.
      y <- symContainer
      constrainExtension y o

      -- Constrain the morphism f so that each input x_i (along with the
      -- context) maps to the corresponding output y_i.
      constrainMorphism f (pair c x) y
