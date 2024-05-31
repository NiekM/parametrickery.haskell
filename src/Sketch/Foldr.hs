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

-- TODO: do we define many different versions of foldr?

-- | Compute the constraint for a @foldr@ sketch.
--
-- This is a slight generalization of Figure 5 of "Example-Based Reasoning
-- About the Realizability of Programs", introducing a context parameter.
--
foldr :: FoldExamples -> ConstraintSet
foldr (FoldExamples examples) = runFresh do

  f <- symMorphism
  e <- symMorphism

  forM_ examples
    \(Mono (FoldExample ctx inputs output)) -> do

    as <- forM (reverse inputs) \x -> do
      a <- symContainer
      constrainExtension a x
      return a

    bs <- replicateM (length inputs + 1) symContainer

    c <- symContainer
    constrainExtension c ctx

    case bs of
      -- If there are intermediate results ...
      (b0 : bs') -> do
        constrainMorphism e c b0
        constrainExtension (last bs) output

        forM_ (zip3 as bs bs') \(a, b, b') -> do
          constrainMorphism f (pair c (pair a b)) b'

      _ -> return ()
