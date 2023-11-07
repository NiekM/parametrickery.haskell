module Symbolic
  ( symbolicContainer, symbolicMorphism
  , makeFoldr, makeMap
  , makeConcatMap
  , makeFoldrE
  , makeMinFoldr
  ) where

import Data.SBV hiding (rotate)
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple qualified as SBV
import Data.Map qualified as Map
import Control.Monad

import Data.Functor.Product
-- import Data.Functor.Const

import Container

import Data.Proxy

-- import Debug.Trace

type SShape f = SBV (RawShape f)

type SPosition f = SBV (RawPosition f)

data SExtension f a where
  SExtension :: Container f =>
    { sShape :: SShape f
    , sPosition :: SPosition f -> SBV a
    } -> SExtension f a

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
symbolicContainer :: forall f a. (Container f, HasKind a)
  => String -> String -> Symbolic (SExtension f a)
symbolicContainer s p = do
  sh <- symbolic s
  constrain $ refine @f Proxy sh
  let pos = sym p
  return $ SExtension sh pos

-- Create a symbolic variable for the extension of a container morphism, given a
-- name for its shape morphism and position morphism.
symbolicMorphism :: forall f g. (Container f, Container g)
  => String -> String -> Symbolic (SMorphism f g)
symbolicMorphism u g = do
  let sh = sym u
  let pos = sym g
  constrain \(Forall s) ->
    refine @f Proxy s .=> refine @g Proxy (sh s)
  constrain \(Forall s) (Forall x) ->
    refine @f Proxy s
    .&& depend @g Proxy (sh s) x
    .=> depend @f Proxy s (pos s x)
  return $ SMorphism sh pos

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
  constrain $ s .== literal (rawShape s')
  forM_ (Map.assocs p') \(k, v) -> do
    constrain $ p (literal (rawPosition k)) .== literal v

-- Unify two symbolic container extensions.
unifyExtension :: forall f a. SExtension f a -> SExtension f a -> Symbolic ()
unifyExtension (SExtension s p) (SExtension t q) = do
  constrain $ s .== t
  constrain \(Forall x) -> do
    depend @f Proxy s x .=> p x .== q x

-- Constrain a symbolic morphism using an input-output example.
constrainExample :: SMorphism f g -> SExtension f a -> SExtension g a -> Symbolic ()
constrainExample f i = unifyExtension (apply f i)

-- * Combinators

makeFoldr :: (Container f, Container g, Container h, SymVal a)
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

-- A version of foldr that keeps both input arguments symbolic.
-- It seems to work correctly, but perhaps there should be two different contexts?
makeFoldrE :: (Container f, Container g, Container h, Container j, SymVal a)
  => h a -> j a -> [f a] -> SMorphism j g -> g a -> SMorphism (Product h (Product f g)) g
  -> String -> Symbolic ()
makeFoldrE ctx_f ctx_e xs e o f s = do

  as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
    a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainExtension a x
    return a

  bs <- forM [0 .. length xs] \i -> do
    symbolicContainer (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

  c <- symbolicContainer (s <> "_c_s") (s <> "_c_p")
  constrainExtension c ctx_f

  d <- symbolicContainer (s <> "_d_s") (s <> "_d_p")
  constrainExtension d ctx_e

  e' <- symbolicContainer (s <> "_e_s") (s <> "_e_p")
  constrainExample e d e'

  case (bs, reverse bs) of
    (b0 : _, bn : _) -> do
      unifyExtension b0 e'
      constrainExtension bn o
    _ -> return ()

  forM_ (zip (zip as bs) (tail bs)) \((a, b), b') -> do
    constrainExample f (pair c (pair a b)) b'

makeMap :: (Container f, Container g, Container h, SymVal a)
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

-- Seems to behave as expected. Can we add context? And composed containers?
-- This is an example of how we can combine propagation with translation.
makeConcatMap :: forall f a. (Container f, SymVal a)
  => [f a] -> [a] -> SMorphism f []
  -> String -> Symbolic ()
makeConcatMap xs ys f s = do

  bs <- forM (zip [0 :: Int ..] xs) \(i, x) -> do
    a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainExtension a x
    b <- symbolicContainer @[] @a (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)
    constrainExample f a b
    return b

  o <- symbolicContainer @[] @a (s <> "_o_s") (s <> "_o_p")
  constrainExtension o ys

  -- This code checks whether concatenating the lists returned by f results in
  -- the output list o.
  -- First we check if their total length is correct.
  constrain $ sum (sShape <$> bs) .== sShape o
  -- Then we check if the position functions match up (after shifting them the
  -- appropriate amounts.)
  let is = scanl (\x y -> x + sShape y) 0 bs
  forM_ (zip is bs) \(i, SExtension n p) -> do
    constrain \(Forall x) -> do
      depend @[] Proxy n x .=> p x .== sPosition o (x + i)

-- makeFilter :: forall f a. (Container f, SymVal a)
--   => [f a] -> [f a] -> SMorphism f (Const Bool)
--   -> String -> Symbolic ()
-- makeFilter xs ys f s = do

--   as <- forM (zip [0 :: Int ..] xs) \(i, x) -> do
--     a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
--     constrainExtension a x
--     return a

--   -- _
--   -- TODO: figure out how this would work

--   bs <- forM (zip [0 :: Int ..] xs) \(i, x) -> do
--     a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
--     constrainExtension a x
--     b <- symbolicContainer @[] @a (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)
--     constrainExample f a b
--     return b

--   o <- symbolicContainer @[] @a (s <> "_o_s") (s <> "_o_p")
--   constrainExtension o ys

--   -- This code checks whether concatenating the lists returned by f results in
--   -- the output list o.
--   -- First we check if their total length is correct.
--   constrain $ sum (sShape <$> bs) .== sShape o
--   -- Then we check if the position functions match up (after shifting them the
--   -- appropriate amounts.)
--   let is = scanl (\x y -> x + sShape y) 0 bs
--   forM_ (zip is bs) \(i, SExtension n p) -> do
--     constrain \(Forall x) -> do
--       depend @[] Proxy n x .=> p x .== sPosition o (x + i)

-- * Minimal results

type MContainer f = (Container f, Metric (RawShape f), Metric (RawPosition f))

minimalContainer :: forall f a. (MContainer f, HasKind a)
  => String -> String -> Symbolic (SExtension f a)
minimalContainer s p = do
  sh <- symbolic s
  minimize ("minimize_" <> s) sh
  constrain $ refine @f Proxy sh
  let pos = sym p
  return $ SExtension sh pos

makeMinFoldr :: (MContainer f, MContainer g, MContainer h, SymVal a)
  => h a -> [f a] -> g a -> g a -> SMorphism (Product h (Product f g)) g
  -> String -> Symbolic ()
makeMinFoldr ctx xs e o f s = do

  as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
    a <- minimalContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)

    constrainExtension a x
    return a

  bs <- forM [0 .. length xs] \i -> do
    minimalContainer (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

  c <- minimalContainer (s <> "_c_s") (s <> "_c_p")
  constrainExtension c ctx

  case (bs, reverse bs) of
    (b0 : _, bn : _) -> do
      constrainExtension b0 e
      constrainExtension bn o
    _ -> return ()

  forM_ (zip (zip as bs) (tail bs)) \((a, b), b') -> do
    constrainExample f (pair c (pair a b)) b'
