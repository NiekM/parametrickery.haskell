{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Module      : Data.SBV.Container
Copyright   : (c) Niek Mulleners 2024
Maintainer  : n.mulleners@uu.nl

Datatypes and helper functions for working with symbolic container functors and container morphisms.

-}
module Data.SBV.Container
  -- * Symbolic container data types
  ( SShape, SPosition
  , SExtension(..), SMorphism(..)
  -- * Creating symbolic values
  , symContainer, symMorphism
  -- * Constraining symbolic containers and morphisms
  , constrainExtension, unifyExtension, constrainMorphism
  -- * Other functions
  , apply, pair
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

-- | A type synonym for symbolic shapes of the 'Data.Container.Core.Container'
-- @f@.
type SShape    f = SBV (Sym (Shape f))

-- | A type synonym for symbolic positions of the
-- 'Data.Container.Core.Container' @f@.
type SPosition f = SBV (Sym (Position f))

-- | A symbolic container extension, the symbolic equivalent of
-- 'Data.Container.Core.Extension'.
--  
-- WARNING: the argument to 'Data.SBV.Container.position' is a
-- 'Data.SBV.Depend.Dep'endent type and care should be taken to never constrain
-- 'SExtension.position' on impossible inputs (those that fail
-- 'Data.SBV.Depend.depend').
-- 
data SExtension f a where
  SExtension :: Container f =>
    { shape    :: SShape f
    , position :: SPosition f -> SBV a
    } -> SExtension f a

-- | A symbolic container morphism.
--
-- WARNING: the arguments to 'Data.SBV.Container.shape' and
-- 'Data.SBV.Container.position' are 'Data.SBV.Refine.Ref'inement and
-- 'Data.SBV.Depend.Dep'endent types and care should be taken to never
-- constrain 'Data.SBV.Container.shape' and 'Data.SBV.Container.position' on
-- impossible inputs (those that fail 'Data.SBV.Refine.refine' or
-- 'Data.SBV.Depend.depend').
--
data SMorphism f g where
  SMorphism :: (Container f, Container g) =>
    { shape    :: SShape f -> SShape g
    , position :: SShape f -> SPosition g -> SPosition f
    } -> SMorphism f g

-- | Create a symbolic variable for the extension of a container.
--
-- WARNING: this function introduces symbolic variables with fresh names of the
-- form @"s_0"@ and @"p_0"@. To avoid naming conflicts, try to refrain from
-- introducing variables with such names.
--
symContainer :: forall m f a.
  (MonadFresh m, SolverContext m, Container f, HasKind a)
  => m (SExtension f a)
symContainer = do
  n <- fresh
  let s = sym $ "s_" <> show n
  let p = sym $ "p_" <> show n
  constrain $ refine @(Shape f) s
  return $ SExtension s p

-- | Create a symbolic variable for the extension of a container morphism.
--
-- WARNING: this function introduces symbolic variables with fresh names of the
-- form @"u_0"@ and @"g_0"@. To avoid naming conflicts, try to refrain from
-- introducing variables with such names.
--
symMorphism :: forall m f g.
  (MonadFresh m, SolverContext m, Container f, Container g) =>
  m (SMorphism f g)
symMorphism = do
  n <- fresh
  let u = sym $ "u_" <> show n
  let g = sym $ "g_" <> show n
  -- Foreach correct input s to u, the output should also be correct.
  constrain \(Forall s) ->
    refine @(Shape f) s .=> refine @(Shape g) (u s)
  -- Foreach correct input s and x, the output should also be correct.
  constrain \(Forall s) (Forall x) ->
    (refine @(Shape f) s .&& depend @(Position g) (u s) x)
    .=> depend @(Position f) s (g s x)
  return $ SMorphism u g

-- | Apply a symbolic morphism to a symbolic container.
apply :: SMorphism f g -> SExtension f a -> SExtension g a
apply (SMorphism u g) (SExtension s p) = SExtension (u s) (p . g s)

-- | Compute the pair of two symbolic containers.
pair :: SymVal a => SExtension f a -> SExtension g a ->
  SExtension (Product f g) a
pair (SExtension s p) (SExtension t q) =
  SExtension (SBV.tuple (s, t)) (SBV.either p q)

-- | Constrain a symbolic container extension to be equal to a concrete
-- container extension.
constrainExtension :: (SymVal a, Monad m, SolverContext m) =>
  SExtension f a -> f a -> m ()
constrainExtension (SExtension s p) c = do
  let Extension s' p' = toContainer c
  constrain $ s .== literal (encode s')
  forM_ (Map.assocs p') \(k, v) -> do
    constrain $ p (literal (encode k)) .== literal v

-- | Constrain two symbolic container extensions to be equal to each other.
unifyExtension :: forall m f a. (Monad m, SolverContext m) =>
  SExtension f a -> SExtension f a -> m ()
unifyExtension (SExtension s p) (SExtension t q) = do
  constrain $ s .== t
  constrain \(Forall x) -> depend @(Position f) s x .=> p x .== q x

-- | Constrain a symbolic morphism using an input-output example.
constrainMorphism :: (Monad m, SolverContext m) =>
  SMorphism f g -> SExtension f a -> SExtension g a -> m ()
constrainMorphism f i = unifyExtension (apply f i)
