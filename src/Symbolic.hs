{-# LANGUAGE TypeFamilies, FunctionalDependencies, UndecidableInstances #-}
module Symbolic (module Symbolic) where

import Types

-- import Debug.Trace

import Data.SBV hiding (rotate)
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple (tuple, untuple)
import Numeric.Natural
import Data.Map qualified as Map
import Data.Void
import Control.Monad
import Data.List (intersperse)

import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Const

import Container

class SymVal (UnRefined a) => Refined a where
  type UnRefined a
  unrefine :: a -> UnRefined a
  refine :: proxy a -> SBV (UnRefined a) -> SBool

symbolicR :: Refined a => proxy a -> String -> Symbolic (SBV (UnRefined a))
symbolicR p s = do
  x <- symbolic s
  constrain $ refine p x
  return x

class (Refined a, SymVal (InDependent a b)) => Dependent a b where
  type InDependent a b
  independ :: a -> b -> InDependent a b
  depend :: proxy a b -> SBV (UnRefined a) -> SBV (InDependent a b) -> SBool

symbolicD :: Dependent a b => proxy a b -> SBV (UnRefined a) -> String -> Symbolic (SBV (InDependent a b))
symbolicD p x s = do
  y <- symbolic s
  constrain $ depend p x y
  return y

instance Refined Void where
  type UnRefined Void = Integer
  unrefine = absurd
  refine _ _ = sFalse

instance Refined () where
  type UnRefined () = Integer
  unrefine _ = 0
  refine _ n = n .== 0

instance (Refined a, Refined b) => Refined (a, b) where
  type UnRefined (a, b) = (UnRefined a, UnRefined b)
  unrefine (x, y) = (unrefine x, unrefine y)
  refine _ a = let (x, y) = untuple a in refine @a undefined x .&& refine @b undefined y

instance Refined Natural where
  type UnRefined Natural = Integer
  unrefine = toInteger
  refine _ n = n .>= 0

instance (Refined k, Refined a) => Dependent k (K a) where
  type InDependent k (K a) = UnRefined a
  independ _ (K a) = unrefine a
  depend _ _ x = refine @a undefined x

instance (Dependent a b, Dependent c d) => Dependent (a, c) (Either b d) where
  type InDependent (a, c) (Either b d) = Either (InDependent a b) (InDependent c d)
  independ (x, y) = either (Left . independ x) (Right . independ y)
  depend _ a = let (x, y) = untuple a in SBV.either (depend @a @b undefined x) (depend @c @d undefined y)

instance Dependent Natural Fin where
  type InDependent Natural Fin = Integer
  independ _ (Fin n) = unrefine n
  depend _ m n = n .>= 0 .&& n .< m

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

io :: forall f g a. SymMorphism f g -> SymExtension f a -> SymExtension g a -> Symbolic ()
io (SymMorphism u g) (SymExtension s p) (SymExtension t q) = do
  constrain $ refine @(Shape f) undefined s
  constrain $ refine @(Shape g) undefined t
  constrain $ u s .== t
  constrain \(Forall x) -> depend @(Shape g) @(Position g) undefined t x .=>
    let y = g s x in depend @(Shape f) @(Position f) undefined s y .&& p y .== q x

symbolicContainer :: (SymContainer f, HasKind a) => String -> String -> Symbolic (SymExtension f a)
symbolicContainer s p = do
  shape <- symbolic s
  let position = sym p
  return $ SymExtension shape position
  
symbolicMorphism :: (SymContainer f, Dependent (Shape g) (Position g))
  => String -> String -> Symbolic (SymMorphism f g)
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

-- extend :: SymVal a => SBV a -> SymExtension f a -> SymExtension (Product Identity f) a 
-- extend x (SymExtension s p) = SymExtension (tuple (literal (unrefine ()), s)) $ SBV.either (const x) p

combine :: SymVal a => SymExtension f a -> SymExtension g a -> SymExtension (Product f g) a
combine (SymExtension s p) (SymExtension t q) = SymExtension (tuple (s, t)) (SBV.either p q)

-- -- foldr f [] [1,2,3] == [2,3]
-- --   f (1, x) == [2,3]
-- --   f (2, y) == x
-- --   f (3, []) == y
-- tail123 :: Symbolic ()
-- tail123 = do
--   let inputContainer = symbolicContainer @(Product Identity []) @Integer
--   let outputContainer = symbolicContainer @[] @Integer

--   f <- symbolicMorphism "u" "g"

--   i0 <- inputContainer "s0" "p0"
--   i1 <- inputContainer "s1" "p1"
--   i2 <- inputContainer "s2" "p2"

--   o1 <- outputContainer "t1" "q1"
--   o0 <- outputContainer "t0" "q0"
--   o2 <- outputContainer "t2" "q2"

--   constrainContainer (toContainer [2, 3]) o0

--   -- eqContainer i0 (extend 1 o1)
--   -- eqContainer i1 (extend 2 o2)
  
--   x0 <- symbolicContainer @Identity @Integer "a0" "b0"
--   x1 <- symbolicContainer @Identity @Integer "a1" "b1"
--   constrainContainer (toContainer (Identity 1)) x0
--   constrainContainer (toContainer (Identity 2)) x1
--   eqContainer i0 (combine x0 o1)
--   eqContainer i1 (combine x1 o2)

--   constrainContainer (toContainer (Pair (Identity 3) [])) i2

--   io f i0 o0
--   io f i1 o1
--   io f i2 o2

-- -- foldr f [] [4,5] == [5]
-- --   f (4, x) == [5]
-- --   f (5, []) == x
-- tail45 :: Symbolic ()
-- tail45 = do
--   let inputContainer = symbolicContainer @(Product Identity []) @Integer
--   let outputContainer = symbolicContainer @[] @Integer

--   f <- symbolicMorphism "u" "g"

--   i0 <- inputContainer "s4" "p4"
--   i1 <- inputContainer "s5" "p5"

--   o0 <- outputContainer "t4" "q4"
--   o1 <- outputContainer "t5" "q5"

--   constrainContainer (toContainer [5]) o0
--   eqContainer i0 (extend 4 o1)
--   constrainContainer (toContainer (Pair (Identity 5) [])) i1

--   io f i0 o0
--   io f i1 o1

-- -- foldr f [] [T,F] == [F]
-- --   f (T, x) == [F]
-- --   f (F, []) == x
-- tailTF :: Symbolic ()
-- tailTF = do
--   let inputContainer = symbolicContainer @(Product Identity []) @Bool
--   let outputContainer = symbolicContainer @[] @Bool

--   f <- symbolicMorphism "u" "g"

--   i0 <- inputContainer "s4" "p4"
--   i1 <- inputContainer "s5" "p5"

--   o0 <- outputContainer "t4" "q4"
--   o1 <- outputContainer "t5" "q5"

--   constrainContainer (toContainer [False]) o0
--   eqContainer i0 (extend sTrue o1)
--   constrainContainer (toContainer (Pair (Identity False) [])) i1

--   io f i0 o0
--   io f i1 o1

-- -- ... f (x, r) == o
-- -- fldr :: forall f g. (Dependent (Shape f) (Position f), Dependent (Shape g) (Position g))
-- --   => SymMorphism (Product f g) g -> Int -> Symbolic ()
-- -- fldr f n = do
-- --   -- let fContainer = symbolicContainer @f @Integer
-- --   -- let gContainer = symbolicContainer @g @Integer

-- --   forM_ [0 .. n] \j -> do
-- --     let tag = (<> show j)
-- --     x <- symbolicContainer @f @Integer (tag "x_s") (tag "x_p")
-- --     r <- symbolicContainer @g @Integer (tag "r_s") (tag "r_p")
-- --     o <- symbolicContainer @g @Integer (tag "o_s") (tag "o_p")
-- --     i <- symbolicContainer @(Product f g) @Integer (tag "i_s") (tag "i_p")
    
-- --     eqContainer i (combine x r)

-- --     io f i o

type Dep f = Dependent (Shape f) (Position f)

-- fld :: forall f g a. (Dep f, Dep g, SymVal a) =>
--   [Extension f a] -> Extension g a -> Extension g a -> SymMorphism (Product f g) g -> String -> Symbolic ()
-- fld xs e o f s = do

--   as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
--     a <- symbolicContainer @f @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
--     constrainContainer x a
--     return a

--   bs <- forM [0 .. length xs] \i -> do
--     symbolicContainer @g @a (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

--   case (bs, reverse bs) of
--     (b0 : _, bn : _) -> do
--       constrainContainer e b0
--       constrainContainer o bn
--     _ -> return ()

--   forM_ (zip (zip as bs) (tail bs)) \((a, b), b') -> do
--     io f (combine a b) b'
  
-- fld' :: forall f g a. (Dep f, Dep g, Container f, Container g, SymVal a) => [f a] -> g a -> g a -> SymMorphism (Product f g) g -> String -> Symbolic ()
-- fld' xs e o = fld (toContainer <$> xs) (toContainer e) (toContainer o) 

tailProof :: Symbolic ()
tailProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeTail :: SymVal a => String -> [a] -> Symbolic ()
    makeTail s xs = fldCtx' @Identity @[] @(Const ()) (Const ()) (Identity <$> xs) [] (tail xs) f ("tail_" <> s)

  -- makeTail @Integer "45678" [4,5,6,7,8]
  makeTail @Integer "4567" [4,5,6,7]
  -- makeTail @Integer "123" [1,2,3]
  makeTail @Bool "TF" [True, False]
  -- makeTail @Bool "T" [True]

-- rotate :: [a] -> [a]
-- rotate [] = []
-- rotate (x:xs) = foldr (\y r -> y:r) [x] xs

-- -- Maybe rotate can be a fold? Or it is too hard to prove
-- rotateProof :: Symbolic ()
-- rotateProof = do
--   f <- symbolicMorphism "u" "g"

--   let
--     makeRotate :: SymVal a => String -> [a] -> Symbolic ()
--     makeRotate s xs = fld' @Identity @[] (Identity <$> xs) [] (rotate xs) f ("rotate_" <> s)

--   makeRotate @Integer "123" [1,2,3]
--   makeRotate @Bool "TF" [True, False]
--   makeRotate @Bool "T" [True]

-- fldCtx :: forall f g h a. (Dep f, Dep g, Dep h, SymVal a) => Extension h a ->
--   [Extension f a] -> Extension g a -> Extension g a -> SymMorphism (Product h (Product f g)) g -> String -> Symbolic ()
-- fldCtx ctx xs e o f s = do

--   as <- forM (zip [0 :: Int ..] (reverse xs)) \(i, x) -> do
--     a <- symbolicContainer @f @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)
--     constrainContainer x a
--     return a

--   bs <- forM [0 .. length xs] \i -> do
--     symbolicContainer @g @a (s <> "_b_s_" <> show i) (s <> "_b_p_" <> show i)

--   c <- symbolicContainer @h @a (s <> "_c_s") (s <> "_c_p")
--   constrainContainer ctx c

--   case (bs, reverse bs) of
--     (b0 : _, bn : _) -> do
--       constrainContainer e b0
--       constrainContainer o bn
--     _ -> return ()

--   forM_ (zip (zip as bs) (tail bs)) \((a, b), b') -> do
--     io f (combine c (combine a b)) b'

-- fldCtx' :: forall f g h a. (Dep f, Dep g, Dep h, Container f, Container g, Container h, SymVal a) =>
--   h a -> [f a] -> g a -> g a -> SymMorphism (Product h (Product f g)) g -> String -> Symbolic ()
-- fldCtx' ctx xs e o = fldCtx (toContainer ctx) (toContainer <$> xs) (toContainer e) (toContainer o) 

fldCtx' :: forall f g h a. (Dep f, Dep g, Dep h, Container f, Container g, Container h, SymVal a) =>
  h a -> [f a] -> g a -> g a -> SymMorphism (Product h (Product f g)) g -> String -> Symbolic ()
fldCtx' ctx xs e o f s = do

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

dropProof :: Symbolic ()
dropProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeDrop :: SymVal a => String -> Int -> [a] -> Symbolic ()
    makeDrop s n xs = fldCtx' @Identity @[] @(Const Natural) (fromIntegral n) (Identity <$> xs) [] (drop n xs) f ("drop_" <> s)

  makeDrop @Integer "2_4567" 2 [4,5,6,7]
  -- makeDrop @Integer "1_123" 1 [1,2,3]
  makeDrop @Integer "2_123" 2 [1,2,3]
  -- makeDrop @Bool "1_TF" 1 [True, False]
  -- makeDrop @Bool "1_T" 1 [True]

intersperseProof :: Symbolic ()
intersperseProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeIntersperse :: SymVal a => String -> a -> [a] -> Symbolic ()
    makeIntersperse s x xs = fldCtx' @Identity @[] @Identity (Identity x) (Identity <$> xs) [] (intersperse x xs) f   
      ("intersperse_" <> s)
  -- makeIntersperse @Integer "3_4567" 3 [4,5,6,7]
  -- makeIntersperse @Integer "4_123" 4 [1,2,3]
  -- makeIntersperse @Bool "T_TF" True [False, False]
  -- makeIntersperse @Bool "F_T" False [True]

  -- Trace complete:
  makeIntersperse @Integer "0_1234" 0 [1,2,3,4]
  makeIntersperse @Integer "0_234" 0 [2,3,4]
  makeIntersperse @Integer "0_34" 0 [3,4]
  makeIntersperse @Integer "0_4" 0 [4]

-- Conclusion
intersperse_ :: a -> [a] -> [a]
intersperse_ x = foldr f []
  where
    f y [] = [y]
    f y (z:zs) = y:x:z:zs


-- mapCtx :: forall f g h a. (Dep f, Dep g, Dep h, SymVal a) => Extension h a ->
--   [(Extension f a, Extension g a)] -> SymMorphism (Product h f) g -> String -> Symbolic ()
-- mapCtx ctx xs f s = do

--   c <- symbolicContainer @h @a (s <> "_c_s") (s <> "_c_p")
--   constrainContainer ctx c

--   forM_ (zip [0 :: Int ..] xs) \(i, (x, y)) -> do
--     a <- symbolicContainer @f @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)  
--     constrainContainer x a
--     b <- symbolicContainer @g @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)  
--     constrainContainer y b
--     io f (combine c a) b
  
-- mapCtx' :: forall f g h a. (Dep f, Dep g, Dep h, Container f, Container g, Container h, SymVal a) =>
--   h a -> [f a] -> [g a] -> SymMorphism (Product h f) g -> String -> Symbolic ()
-- mapCtx' ctx xs ys f s = do
--   when (length xs /= length ys) $ constrain sFalse
--   mapCtx (toContainer ctx) (zip (toContainer <$> xs) (toContainer <$> ys)) f s

mapCtx :: forall f g h a. (Dep f, Dep g, Dep h, Container f, Container g, Container h, SymVal a) =>
  h a -> [f a] -> [g a] -> SymMorphism (Product h f) g -> String -> Symbolic ()
mapCtx ctx xs ys f s = do

  when (length xs /= length ys) $ constrain sFalse

  c <- symbolicContainer @h @a (s <> "_c_s") (s <> "_c_p")
  constrainContainer (toContainer ctx) c

  forM_ (zip [0 :: Int ..] (zip xs ys)) \(i, (x, y)) -> do
    a <- symbolicContainer @f @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)  
    constrainContainer (toContainer x) a
    b <- symbolicContainer @g @a (s <> "_a_s_" <> show i) (s <> "_a_p_" <> show i)  
    constrainContainer (toContainer y) b
    io f (combine c a) b

revProof :: Symbolic ()
revProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeRev :: SymVal a => String -> [a] -> Symbolic ()
    makeRev s xs = mapCtx @Identity @Identity @[] xs (Identity <$> xs) (Identity <$> reverse xs) f ("rev_" <> s)

  -- makeRev @Integer "palyndrome" [1,2,3,2,1]
  makeRev @Integer "45678" [4,5,6,7,8]
  -- makeRev @Integer "4567" [4,5,6,7]
  -- makeRev @Integer "123" [1,2,3]
  -- makeRev @Bool "TF" [True, False]
  -- makeRev @Bool "T" [True]

mapProof :: Symbolic ()
mapProof = do
  f <- symbolicMorphism "u" "g"

  -- let
  --   makeMap :: SymVal a => String -> [a] -> Symbolic ()
  --   makeMap s xs = mapCtx @Identity @Identity @[] xs (Identity <$> xs) (Identity <$> reverse xs) f ("rev_" <> s)

  mapCtx @Identity @Identity @[] @Integer [1,2,3] [1,2,3] [3,2,1] f "rev123"

  -- makeRev @Integer "palyndrome" [1,2,3,2,1]
  -- makeRev @Integer "45678" [4,5,6,7,8]
  -- makeRev @Integer "4567" [4,5,6,7]
  -- makeRev @Integer "123" [1,2,3]
  -- makeRev @Bool "TF" [True, False]
  -- makeRev @Bool "T" [True]