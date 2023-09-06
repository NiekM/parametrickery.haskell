module Symbolic
  ( symbolicContainer, symbolicMorphism
  , makeFoldr, makeMap
  ) where

import Data.SBV hiding (rotate)
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple qualified as SBV
import Data.Map qualified as Map
import Control.Monad

import Data.Functor.Product

import Container
import Dependent

type SContainer f = (Container f, Dependent (Shape f) (Position f))

type RawShape f = UnRefined (Shape f)
type RawPosition f = InDependent (Shape f) (Position f)

type SShape f = SBV (RawShape f)

type SPosition f = SBV (RawPosition f)

data SExtension f a where
  SExtension :: SContainer f
    => SShape f -> (SPosition f -> SBV a) -> SExtension f a

data SMorphism f g where
  SMorphism :: (SContainer f, SContainer g)
    => (SShape f -> SShape g)
    -> (SShape f -> SPosition g -> SPosition f)
    -> SMorphism f g

-- Create a symbolic variable for the extension of a container, given a name for
-- its shape and its position function.
-- WARNING: the position function is a dynamically dependent function and should
-- never be constrained on impossible positions (those that fail the dependency
-- check).
symbolicContainer :: forall f a. (SContainer f, HasKind a)
  => String -> String -> Symbolic (SExtension f a)
symbolicContainer s p = do
  shape <- symbolic s
  constrain $ refine @(Shape f) undefined shape
  let position = sym p
  return $ SExtension shape position
  
-- Create a symbolic variable for the extension of a container morphism, given a
-- name for its shape morphism and position morphism.
symbolicMorphism :: forall f g. (SContainer f, SContainer g)
  => String -> String -> Symbolic (SMorphism f g)
symbolicMorphism u g = do
  let shape = sym u
  let position = sym g
  constrain \(Forall s) ->
    refine @(Shape f) undefined s .=> refine @(Shape g) undefined (shape s)
  constrain \(Forall s) (Forall x) ->
    refine @(Shape f) undefined s
    .&& depend @(Shape g) @(Position g) undefined (shape s) x
    .=> depend @(Shape f) @(Position f) undefined s (position s x)
  return $ SMorphism shape position

-- Apply a symbolic morphism to a symbolic container.
apply :: SMorphism f g -> SExtension f a -> SExtension g a
apply (SMorphism u g) (SExtension s p) = SExtension (u s) (p . g s)

-- The pair of two symbolic containers.
pair :: SymVal a => SExtension f a -> SExtension g a ->
  SExtension (Product f g) a
pair (SExtension s p) (SExtension t q) =
  SExtension (SBV.tuple (s, t)) (SBV.either p q)

-- Constrain a symbolic container extension to be equal to a concrete container
-- extension.
constrainExtension :: SymVal a => SExtension f a -> f a -> Symbolic ()
constrainExtension (SExtension s p) c = do
  let Extension s' p' = toContainer c
  constrain $ s .== literal (unrefine s')
  forM_ (Map.assocs p') \(k, v) -> do
    constrain $ p (literal (independ s' k)) .== literal v

-- Unify two symbolic container extensions.
unifyExtension :: forall f a. SExtension f a -> SExtension f a -> Symbolic ()
unifyExtension (SExtension s p) (SExtension t q) = do
  constrain $ s .== t
  constrain \(Forall x) -> do
    depend @(Shape f) @(Position f) undefined s x .=> p x .== q x

-- Constrain a symbolic morphism using an input-output example.
constrainExample :: SMorphism f g -> SExtension f a -> SExtension g a -> Symbolic ()
constrainExample f i o = unifyExtension (apply f i) o

-- * Combinators

makeFoldr :: (SContainer f, SContainer g, SContainer h, SymVal a)
  => h a -> [f a] -> g a -> g a -> SMorphism (Product h (Product f g)) g
  -> String -> Symbolic ()
makeFoldr ctx xs e o f s = do

  as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
    a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainExtension a x
    return a

  bs <- forM [0 .. length xs] \i -> do
    symbolicContainer (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

  c <- symbolicContainer (s <> "_c_s") (s <> "_c_p")
  constrainExtension c ctx

  case (bs, reverse bs) of
    (b0 : _, bn : _) -> do
      constrainExtension b0 e
      constrainExtension bn o
    _ -> return ()

  forM_ (zip (zip as bs) (tail bs)) \((a, b), b') -> do
    constrainExample f (pair c (pair a b)) b'

makeMap :: (SContainer f, SContainer g, SContainer h, SymVal a)
  => h a -> [f a] -> [g a] -> SMorphism (Product h f) g
  -> String -> Symbolic ()
makeMap ctx xs ys f s = do

  when (length xs /= length ys) $ constrain sFalse

  c <- symbolicContainer (s <> "_c_s") (s <> "_c_p")
  constrainExtension c ctx

  forM_ (zip [0 :: Int ..] (zip xs ys)) \(i, (x, y)) -> do
    a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainExtension a x
    b <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainExtension b y
    constrainExample f (pair c a) b