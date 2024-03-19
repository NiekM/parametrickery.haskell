{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Pipeline where

import Control.Monad

import Data.SBV hiding (output)

import Data.SBV.Container

import Base
import Data.Container
import Data.Mono

-- foldr : (c a -> f a -> g a -> g a) -> (d a -> g a) -> [f a] -> g a
type FoldInput c d f g = Product (Product (Product c d) (Compose [] f)) g

{-# COMPLETE FoldInput #-}
pattern FoldInput :: c a -> d a -> [f a] -> g a -> FoldInput c d f g a
pattern FoldInput c d f g = Pair (Pair (Pair c d) (Compose f)) g

data FoldInputs = forall c d f g.
  (Container c, Container d, Container f, Container g) =>
  FoldInputs [Mono SymVal (FoldInput c d f g)]

foldr :: FoldInputs -> ConstraintSet
foldr (FoldInputs examples) = freshEnvironment do

  f <- symMorphism
  e <- symMorphism

  forM_ examples
    \(Mono (FoldInput ctx_f ctx_e inputs output)) -> do

    as <- forM (reverse inputs) \x -> do
      a <- symContainer
      constrainExtension a x
      return a

    bs <- replicateM (length inputs + 1) $ symContainer

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
