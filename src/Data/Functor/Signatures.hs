{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Functor.Signatures where

import Data.List       qualified as List
import Data.Map.Strict qualified as Map

import Base
import Constraint
import Pretty

------ Signatures ------

---- Expressions ----

type Exp t = Each [Eq, Ord, Show] t

-- Expression signatures
data ExpSig t where
  Nat :: ExpSig Natural
  Str :: ExpSig String

data AnyExp where
  AnyExp :: forall t. Each [Eq, Ord, Show] t => ExpSig t -> t -> AnyExp

instance Eq AnyExp where
  AnyExp s x == AnyExp t y = case (s, t) of
    (Nat, Nat) -> x == y
    (Str, Str) -> x == y
    _ -> False

instance Ord AnyExp where
  AnyExp s x `compare` AnyExp t y = case (s, t) of
    (Nat, Nat) -> x `compare` y
    (Str, Str) -> x `compare` y
    _ -> compare (ctrIndex s) (ctrIndex t)
    where
      ctrIndex :: ExpSig t -> Natural
      ctrIndex = \case Nat -> 0; Str -> 1

instance Show AnyExp where
  show (AnyExp _ x) = show x

---- Functors ----

type Fun f =
  Each [Functor, Foldable, Traversable, Eq1, Ord1, Show1, Pretty] f

type Container f =
  Each [Functor, Foldable, Traversable, Eq1, Ord1, Show1, Pretty] f

-- Functor signatures
data FunSig f where
  I :: FunSig Identity
  K :: Exp t => ExpSig t -> FunSig (Const t)
  P :: (Fun f, Fun g) => FunSig f -> FunSig g -> FunSig (Product f g)
  S :: (Fun f, Fun g) => FunSig f -> FunSig g -> FunSig (Sum f g)
  L :: Fun f => FunSig f -> FunSig (Compose [] f)

data AnyFun a where
  AnyFun :: forall f a. Container f => FunSig f -> f a -> AnyFun a

instance Functor AnyFun where
  fmap f (AnyFun s x) = AnyFun s (fmap f x)

instance Foldable AnyFun where
  foldMap f (AnyFun _ x) = foldMap f x

instance Traversable AnyFun where
  traverse f (AnyFun s x) = AnyFun s <$> traverse f x

instance Eq a => Eq (AnyFun a) where
  (==) = liftEq (==)

instance Eq1 AnyFun where
  liftEq eq (AnyFun s a) (AnyFun t b) = case (s, t, a, b) of
    (I, I, x, y) -> liftEq eq x y
    (K k, K l, Const x, Const y) -> AnyExp k x == AnyExp l y
    (P s1 s2, P t1 t2, Pair x1 x2, Pair y1 y2)
      -> liftEq eq (AnyFun s1 x1) (AnyFun t1 y1)
      && liftEq eq (AnyFun s2 x2) (AnyFun t2 y2)
    (S s1 _, S t1 _, InL x, InL y)
      -> liftEq eq (AnyFun s1 x) (AnyFun t1 y)
    (S _ s2, S _ t2, InR x, InR y)
      -> liftEq eq (AnyFun s2 x) (AnyFun t2 y)
    (L s1, L t1, Compose xs, Compose ys)
      -> liftEq (\x y -> liftEq eq (AnyFun s1 x) (AnyFun t1 y)) xs ys
    _ -> False

instance Ord a => Ord (AnyFun a) where
  compare = liftCompare compare

instance Ord1 AnyFun where
  liftCompare cmp (AnyFun s a) (AnyFun t b) = case (s, t, a, b) of
    (I, I, x, y) -> liftCompare cmp x y
    (K k, K l, Const x, Const y) -> AnyExp k x `compare` AnyExp l y
    (P s1 s2, P t1 t2, Pair x1 x2, Pair y1 y2)
      -> liftCompare cmp (AnyFun s1 x1) (AnyFun t1 y1)
      <> liftCompare cmp (AnyFun s2 x2) (AnyFun t2 y2)
    (S s1 _, S t1 _, InL x, InL y)
      -> liftCompare cmp (AnyFun s1 x) (AnyFun t1 y)
    (S _ s2, S _ t2, InR x, InR y)
      -> liftCompare cmp (AnyFun s2 x) (AnyFun t2 y)
    (L s1, L t1, Compose xs, Compose ys)
      -> liftCompare (\x y -> liftCompare cmp (AnyFun s1 x) (AnyFun t1 y)) xs ys
    _ -> ctrIndex s `compare` ctrIndex t
    where
      ctrIndex :: FunSig f -> Natural
      ctrIndex = \case I -> 0; K{} -> 1; P{} -> 2; S{} -> 3; L{} -> 4

instance Show a => Show (AnyFun a) where
  show x = liftShowsPrec showsPrec showList 0 x ""

instance Show1 AnyFun where
  liftShowsPrec sp sl p (AnyFun _ x) =
    liftShowsPrec sp sl p x

instance Pretty AnyFun where
  pretty p (AnyFun _ x) = pretty p x

newtype Ctx a = Ctx (Map String (AnyFun a))

instance Functor Ctx where
  fmap f (Ctx m) = Ctx $ fmap (fmap f) m

instance Foldable Ctx where
  foldMap f (Ctx m) = foldMap (foldMap f) m

instance Traversable Ctx where
  traverse f (Ctx m) = Ctx <$> traverse (traverse f) m

instance Show a => Show (Ctx a) where
  show x = liftShowsPrec showsPrec showList 0 x ""

instance Show1 Ctx where
  liftShowsPrec sp sl _ (Ctx c) s =
    '{' : List.intercalate ", " (showMap <$> Map.assocs c) ++ '}' : s
    where showMap (k, v) = k ++ " = " ++ liftShowsPrec sp sl 0 v ""

instance Eq a => Eq (Ctx a) where
  (==) = liftEq (==)

instance Eq1 Ctx where
  liftEq eq (Ctx m) (Ctx n) = liftEq (liftEq eq) m n

instance Ord a => Ord (Ctx a) where
  compare = liftCompare compare

instance Ord1 Ctx where
  liftCompare cmp (Ctx m) (Ctx n) = liftCompare (liftCompare cmp) m n

instance Pretty Ctx where
  pretty _ (Ctx c) s =
    '{' : List.intercalate ", " (showMap <$> Map.assocs c) ++ '}' : s
    where showMap (k, v) = k ++ " = " ++ pretty 0 v ""

------ Examples ------

getList :: AnyFun a -> [AnyFun a]
getList = \case
  AnyFun (L s) (Compose xs) -> AnyFun s <$> xs
  _ -> []

example :: Ctx Int
example = Ctx $ Map.fromList
  [ ("xs", AnyFun (L I) $ Compose [1, 2, 3])
  , ("x", AnyFun I 4)
  , ("e", AnyFun (S (K Str) I) $ InL "Error")
  ]

-- >>> pretty 0 example ""
-- "{e = Left \"Error\", x = 4, xs = [1,2,3]}"

ex2 :: AnyFun Int
ex2 = AnyFun (P (S (S I (K Str)) I) (L I))
  $ Pair (InL (InR "Hello")) (Compose [1,2,3])

-- >>> pretty 0 ex2 ""
-- "(Left (Right \"Hello\"),[1,2,3])"

extractEach :: Ord k => Map k v -> [(k, v, Map k v)]
extractEach m = Map.assocs m <&> \(k, v) -> (k, v, Map.delete k m)

listArguments :: Ctx a -> [(String, [AnyFun a], Ctx a)]
listArguments (Ctx ctx) = extractEach ctx >>= \(a, f, ctx') -> case f of
  AnyFun (L s) (Compose xs) -> [(a, AnyFun s <$> xs, Ctx ctx')]
  _ -> []

-- TODO: use these better contexts to automatically generate possible
-- refinements:
--
--  1. Scope pruning: it should be easy enough to check realizability with scope
--     pruning.
--  2. Sketching: foldr, but also others. Can we create a general framework for
--     sketching where one container morphism of a specific shape is refined to
--     zero or more other container morphisms?
--
-- - What is a refinement? Perhaps it is a function from a container morphism
--   that may return any number of morphisms. (i.e. Morph -> Maybe [Morph])
-- - How do we represent a refinement being instantiated in different ways (i.e.
--   a fold over different lists in scope)?
-- - How do we represent the different ways in which a refinement can fail (and
--   how does this differ from not being applicable)? We could say that a
--   refinement fails if any of the resulting morphisms are unrealizable. But is
--   this any different from not being applicable? I guess so, since failure of
--   some refinements may influence the choice of other refinements.
-- - How do we handle type abstractions? They are not dependent on the context.
-- - How do we show the relationship between different refinements? For example,
--   foldr can only be applied to a list, but there may be multiple lists in
--   scope. There is a relationship between map and foldr, but we can only
--   reason about this if we consider the same list.
-- - How do we combine refinements that follow each other? Do we always consider
--   each refinement separately or can we group them, e.g. using a sketch
--   followed by pruning to create a slightly different sketch.
--
