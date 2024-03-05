module Symbolic
  ( symbolicContainer, symbolicMorphism
  , makeFoldr, makeMap
  , makeConcatMap
  , makeFoldrE
  , makeMinFoldr
  , check
  ) where

import Data.SBV hiding (rotate)
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple qualified as SBV
import Data.Map qualified as Map
import Control.Monad

import Base

import Data.Container
import Data.SBV.Encode
import Data.SBV.Depend (Dep(dep))
import Data.SBV.Refine (Ref(ref))

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
symbolicContainer :: forall f a. (Container f, HasKind a)
  => String -> String -> Symbolic (SExtension f a)
symbolicContainer s p = do
  sh <- symbolic s
  constrain $ ref @(Shape f) Proxy sh
  let pos = sym p
  return $ SExtension sh pos

-- Create a symbolic variable for the extension of a container morphism, given a
-- name for its shape morphism and position morphism.
symbolicMorphism :: forall f g. (Container f, Container g)
  => String -> String -> Symbolic (SMorphism f g)
symbolicMorphism u g = do
  let sh = sym u
  let pos = sym g
  -- Foreach correct input s to sh, the output should also be correct.
  constrain \(Forall s) ->
    ref @(Shape f) Proxy s .=> ref @(Shape g) Proxy (sh s)
  -- Foreach correct input s and x, the output should also be correct.
  constrain \(Forall s) (Forall x) ->
    (ref @(Shape f) Proxy s .&& dep @(Position g) Proxy (sh s) x)
    .=> dep @(Position f) Proxy s (pos s x)
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
constrainExtension :: SymVal a => SExtension f a -> f a -> ConstraintSet
constrainExtension (SExtension s p) c = do
  let Extension s' p' = toContainer c
  constrain $ s .== literal (encode s')
  forM_ (Map.assocs p') \(k, v) -> do
    constrain $ p (literal (encode k)) .== literal v

-- Unify two symbolic container extensions.
unifyExtension :: forall f a. SExtension f a -> SExtension f a -> ConstraintSet
unifyExtension (SExtension s p) (SExtension t q) = do
  constrain $ s .== t
  constrain \(Forall x) -> do
    dep @(Position f) Proxy s x .=> p x .== q x

-- Constrain a symbolic morphism using an input-output example.
constrainExample :: SMorphism f g -> SExtension f a -> SExtension g a
  -> ConstraintSet
constrainExample f i = unifyExtension (apply f i)

-- * Combinators

-- TODO: why is it so hard to define makeFoldr in terms of makeFoldrE?
-- makeFoldr :: (Container f, Container g, Container h, SymVal a)
--   => h a -> [f a] -> g a -> g a -> SMorphism (Product h (Product f g)) g
--   -> String -> ConstraintSet
-- makeFoldr ctx xs e o f s = do

--   e' <- symbolicMorphism "u_e" "g_e"
--   constrainExtension (apply e' (SExtension 0 _)) e

--   makeFoldrE @_ @_ @_ @(Const ()) ctx (Const ()) xs e' o f s

--
-- Perhaps the problem is not with having unknown shapes, but rather just that
-- the constraints put on quantified values are too difficult to figure out that
-- they are finitary.
--
-- NOTE: this should never take too long! since every example has a fixed shape,
-- there should be a finite number of positions, which we can simply enumerate, right?
-- This should make the solver much easier, perhaps we can generate a custom datatype
-- that enumerates all possible positions given a specific shape? This should work for
-- both map and shape-complete foldr! Alternatively, this can just be an integer
-- with some constraints. That way, we do not have to figure out `u`, as it
-- follows from the input-outputs, but rather just find a valid `g`.
--
-- For example: Just [1,2,3] -> Just [1]
--          u : Just 3 -> Just 1
--          g : Fin 1 -> Fin 3
--  constraint: g (0) == 0
--
-- Alternative: introduce one variable for each position?
--
-- It seems that this ignores type inhabitation. Is that okay?
--
check :: (Container f, Container g, SymVal a) => [(f a, g a)] -> ConstraintSet
check xs = do
  f <- symbolicMorphism "u" "g"
  forM_ (zip [0 :: Int ..] xs) \(n, (i, o)) -> do
    c <- symbolicContainer ("s_" <> show n) ("p_" <> show n)
    constrainExtension c i
    d <- symbolicContainer ("t_" <> show n) ("q_" <> show n)
    constrainExtension d o
    constrainExample f c d

makeFoldr :: (Container f, Container g, Container h, SymVal a)
  => h a -> [f a] -> g a -> g a -> SMorphism (Product h (Product f g)) g
  -> String -> ConstraintSet
makeFoldr ctx xs e o f s = do

  -- For each input, create a symbolic container that is constrained to that input.
  as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
    a <- symbolicContainer (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainExtension a x
    return a

  -- Create a symbolic container for each of the intermediate results.
  bs <- forM [0 .. length xs] \i -> do
    symbolicContainer (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

  -- Create a symbolic container constrained to the context.
  c <- symbolicContainer (s <> "_c_s") (s <> "_c_p")
  constrainExtension c ctx

  case (bs, reverse bs) of
    (b0 : bs', bn : _) -> do
      -- Constrain the first intermediate result to the base case.
      constrainExtension b0 e
      -- Constrain the last intermediate result to the output.
      constrainExtension bn o

      -- Constrain f such that, for each i, f (ctx, a_i, b_i) == b_i+1
      forM_ (zip3 as bs bs') \(a, b, b') -> do
        constrainExample f (pair c (pair a b)) b'

    _ -> return ()

-- A version of foldr that keeps both input arguments symbolic.
makeFoldrE :: (Container f, Container g, Container h, Container j, SymVal a)
  => h a -> j a -> [f a] -> SMorphism j g -> g a -> SMorphism (Product h (Product f g)) g
  -> String -> ConstraintSet
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
    (b0 : bs', bn : _) -> do
      unifyExtension b0 e'
      constrainExtension bn o

      forM_ (zip3 as bs bs') \(a, b, b') -> do
        constrainExample f (pair c (pair a b)) b'

    _ -> return ()

makeMap :: (Container f, Container g, Container h, SymVal a)
  => h a -> [f a] -> [g a] -> SMorphism (Product h f) g
  -> String -> ConstraintSet
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

sShape :: SExtension f a -> SShape f
sShape (SExtension s _) = s

sPosition :: SExtension f a -> SPosition f -> SBV a
sPosition (SExtension _ p) = p

-- Seems to behave as expected. Can we add context? And composed containers?
-- This is an example of how we can combine propagation with translation.
makeConcatMap :: forall f a. (Container f, SymVal a)
  => [f a] -> [a] -> SMorphism f []
  -> String -> ConstraintSet
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
      dep @(Position []) Proxy n x .=> p x .== sPosition o (x + i)

-- makeFilter :: forall f a. (Container f, SymVal a)
--   => [f a] -> [f a] -> SMorphism f (Const Bool)
--   -> String -> ConstraintSet
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

type MContainer f =
  (Container f, Metric (Sym (Shape f)), Metric (Sym (Position f)))

minimalContainer :: forall f a. (MContainer f, HasKind a)
  => String -> String -> Symbolic (SExtension f a)
minimalContainer s p = do
  sh <- symbolic s
  minimize ("minimize_" <> s) sh
  constrain $ ref @(Shape f) Proxy sh
  let pos = sym p
  return $ SExtension sh pos

makeMinFoldr :: (MContainer f, MContainer g, MContainer h, SymVal a)
  => h a -> [f a] -> g a -> g a -> SMorphism (Product h (Product f g)) g
  -> String -> ConstraintSet
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
    (b0 : bs', bn : _) -> do
      constrainExtension b0 e
      constrainExtension bn o

      forM_ (zip3 as bs bs') \(a, b, b') -> do
        constrainExample f (pair c (pair a b)) b'

    _ -> return ()
