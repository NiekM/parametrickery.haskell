module Symbolic (module Symbolic) where

import Data.SBV hiding (rotate)
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple qualified as SBV
import Data.Map qualified as Map
import Control.Monad

import Data.Functor.Product

import Container
import Dependent

type SymContainer f = (Container f, Dependent (Shape f) (Position f))

type RawShape f = UnRefined (Shape f)
type RawPosition f = InDependent (Shape f) (Position f)

type SymShape f = SBV (RawShape f)

type SymPosition f = SBV (RawPosition f)

data SymExtension f a where
  SymExtension :: Dependent (Shape f) (Position f) =>
    { sShape :: SymShape f
    , sPosition :: SymPosition f -> SBV a
    } -> SymExtension f a

data SymMorphism f g where
  SymMorphism ::
    ( Dependent (Shape f) (Position f)
    , Dependent (Shape g) (Position g)
    ) =>
    { sShapes :: SymShape f -> SymShape g
    , sPositions :: SymShape f -> SymPosition g -> SymPosition f
    } -> SymMorphism f g

-- TODO: now only io checks the refinement constraints.
-- The shape constraints can be handled by 'symbolicContainer' as well,
-- but the position constraints are more difficult to handle elsewhere.
-- Perhaps the position constraints are just needed in 'symbolicMorphism'?

io :: forall f g a. SymMorphism f g -> SymExtension f a -> SymExtension g a -> Symbolic ()
io (SymMorphism u g) (SymExtension s p) (SymExtension t q) = do
  constrain $ refine @(Shape f) undefined s
  constrain $ refine @(Shape g) undefined t
  constrain $ u s .== t
  constrain \(Forall x) -> depend @(Shape g) @(Position g) undefined t x .=>
    let y = g s x in depend @(Shape f) @(Position f) undefined s y .&& p y .== q x

-- Create a symbolic variable for the extension of a container, given a name for
-- its shape and its indexing function.
-- NOTE: this does not constrain the shapes and positions based on their dependencies.
symbolicContainer :: (SymContainer f, HasKind a) => String -> String -> Symbolic (SymExtension f a)
symbolicContainer s p = do
  shape <- symbolic s
  let position = sym p
  return $ SymExtension shape position
  
-- Create a symbolic variable for the extension of a container morphism, given a
-- name for its shape morphism and position morphism.
-- NOTE: this does not constrain the shapes and positions based on their dependencies.
symbolicMorphism :: (SymContainer f, SymContainer g) => String -> String -> Symbolic (SymMorphism f g)
symbolicMorphism u g = do
  let shape = sym u
  let position = sym g
  return $ SymMorphism shape position

constrainContainer :: SymVal a => Extension f a -> SymExtension f a -> Symbolic ()
constrainContainer (Extension s p) (SymExtension s' p') = do
  constrain $ s' .== literal (unrefine s)
  forM_ (Map.assocs p) \(k, v) -> constrain $ p' (literal (independ s k)) .== literal v

eqContainer :: forall f a. SymExtension f a -> SymExtension f a -> Symbolic ()
eqContainer (SymExtension s p) (SymExtension t q) = do
  constrain $ s .== t
  constrain \(Forall x) -> depend @(Shape f) @(Position f) undefined s x .=> p x .== q x

combine :: SymVal a => SymExtension f a -> SymExtension g a -> SymExtension (Product f g) a
combine (SymExtension s p) (SymExtension t q) = SymExtension (SBV.tuple (s, t)) (SBV.either p q)

-- * Combinators

makeFoldr :: forall f g h a. (SymContainer f, SymContainer g, SymContainer h, SymVal a) =>
  h a -> [f a] -> g a -> g a -> SymMorphism (Product h (Product f g)) g -> String -> Symbolic ()
makeFoldr ctx xs e o f s = do

  as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
    a <- symbolicContainer @f @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
    constrainContainer (toContainer x) a
    return a

  bs <- forM [0 .. length xs] \i -> do
    symbolicContainer @g @a (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

  c <- symbolicContainer @h @a (s <> "_c_s") (s <> "_c_p")
  constrainContainer (toContainer ctx) c

  case (bs, reverse bs) of
    (b0 : _, bn : _) -> do
      constrainContainer (toContainer e) b0
      constrainContainer (toContainer o) bn
    _ -> return ()

  forM_ (zip (zip as bs) (tail bs)) \((a, b), b') -> do
    io f (combine c (combine a b)) b'

makeMap :: forall f g h a. (SymContainer f, SymContainer g, SymContainer h, SymVal a) =>
  h a -> [f a] -> [g a] -> SymMorphism (Product h f) g -> String -> Symbolic ()
makeMap ctx xs ys f s = do

  when (length xs /= length ys) $ constrain sFalse

  c <- symbolicContainer @h @a (s <> "_c_s") (s <> "_c_p")
  constrainContainer (toContainer ctx) c

  forM_ (zip [0 :: Int ..] (zip xs ys)) \(i, (x, y)) -> do
    a <- symbolicContainer @f @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)  
    constrainContainer (toContainer x) a
    b <- symbolicContainer @g @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)  
    constrainContainer (toContainer y) b
    io f (combine c a) b