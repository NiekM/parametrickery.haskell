{-# OPTIONS_GHC -Wno-orphans #-}

module Data.SBV.Container
  ( SShape, SPosition
  , SExtension, SMorphism
  , apply, pair
  , constrainExtension, unifyExtension, constrainExample
  , symContainer, symMorphism
  ) where

import Control.Monad
import Control.Monad.Fresh
import Data.Map qualified as Map

import Data.SBV (Forall(..))
import Data.SBV.Internals
import Data.SBV.Trans
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple  qualified as SBV

import Data.SBV.Depend
import Data.Container.Core

import Base

type SShape    f = SBV (Sym (Shape f))
type SPosition f = SBV (Sym (Position f))

data SExtension f a where
  SExtension :: Container f
    => SShape f
    -> (SPosition f -> SBV a)
    -> SExtension f a

data SMorphism f g where
  SMorphism :: (Container f, Container g)
    => (SShape f -> SShape g)
    -> (SShape f -> SPosition g -> SPosition f)
    -> SMorphism f g

-- Create a symbolic variable for the extension of a container, given a name for
-- its shape and its position function.
-- WARNING: the position function is a dynamically dependent function and should
-- never be constrained on impossible positions (those that fail the dependency
-- check).
symContainer :: forall m f a.
  (MonadFresh m, SolverContext m, Container f, HasKind a)
  => m (SExtension f a)
symContainer = do
  n <- fresh
  let s = sym $ "s_" <> show n
  let p = sym $ "p_" <> show n
  constrain $ ref @(Shape f) Proxy s
  return $ SExtension s p

-- Create a symbolic variable for the extension of a container morphism, given a
-- name for its shape morphism and position morphism.
symMorphism :: forall m f g.
  (MonadFresh m, SolverContext m, Container f, Container g) =>
  m (SMorphism f g)
symMorphism = do
  n <- fresh
  let u = sym $ "u_" <> show n
  let g = sym $ "g_" <> show n
  -- Foreach correct input s to u, the output should also be correct.
  constrain \(Forall s) ->
    ref @(Shape f) Proxy s .=> ref @(Shape g) Proxy (u s)
  -- Foreach correct input s and x, the output should also be correct.
  constrain \(Forall s) (Forall x) ->
    (ref @(Shape f) Proxy s .&& dep @(Position g) Proxy (u s) x)
    .=> dep @(Position f) Proxy s (g s x)
  return $ SMorphism u g

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
constrainExtension :: (SymVal a, Monad m, SolverContext m) =>
  SExtension f a -> f a -> m ()
constrainExtension (SExtension s p) c = do
  let Extension s' p' = toContainer c
  constrain $ s .== literal (encode s')
  forM_ (Map.assocs p') \(k, v) -> do
    constrain $ p (literal (encode k)) .== literal v

-- Unify two symbolic container extensions.
unifyExtension :: forall m f a. (Monad m, SolverContext m) =>
  SExtension f a -> SExtension f a -> m ()
unifyExtension (SExtension s p) (SExtension t q) = do
  constrain $ s .== t
  constrain \(Forall x) -> dep @(Position f) Proxy s x .=> p x .== q x

-- Constrain a symbolic morphism using an input-output example.
constrainExample :: (Monad m, SolverContext m) =>
  SMorphism f g -> SExtension f a -> SExtension g a -> m ()
constrainExample f i = unifyExtension (apply f i)
