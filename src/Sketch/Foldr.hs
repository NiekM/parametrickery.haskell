module Sketch.Foldr where

import Control.Monad
import Control.Monad.Fresh

import Data.SBV hiding (output)

import Data.SBV.Container

import Base
import Data.Container
import Data.Mono

type FoldExample c d f g = Product (Product (Product c d) (Compose [] f)) g

{-# COMPLETE FoldExample #-}
pattern FoldExample :: c a -> d a -> [f a] -> g a -> FoldExample c d f g a
pattern FoldExample c d f g = Pair (Pair (Pair c d) (Compose f)) g

data FoldExamples = forall c d f g.
  (Container c, Container d, Container f, Container g) =>
  FoldExamples [Mono SymVal (FoldExample c d f g)]

foldr :: FoldExamples -> ConstraintSet
foldr (FoldExamples examples) = runFresh do

  f <- symMorphism
  e <- symMorphism

  forM_ examples
    \(Mono (FoldExample ctx_f ctx_e inputs output)) -> do

    as <- forM (reverse inputs) \x -> do
      a <- symContainer
      constrainExtension a x
      return a

    bs <- replicateM (length inputs + 1) symContainer

    c <- symContainer
    constrainExtension c ctx_f

    d <- symContainer
    constrainExtension d ctx_e

    case (bs, reverse bs) of
      (b0 : bs', bn : _) -> do
        constrainExample e d b0
        constrainExtension bn output

        forM_ (zip3 as bs bs') \(a, b, b') -> do
          constrainExample f (pair c (pair a b)) b'

      _ -> return ()