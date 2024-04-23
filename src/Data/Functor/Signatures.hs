{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Functor.Signatures where

import Data.List       qualified as List
import Data.Map.Strict qualified as Map

import Base
import Constraint
import Pretty

------ Signatures ------

data Comparison x y where
  Lesser  :: Comparison x y
  Equal   :: (x ~ y) => Comparison x y
  Greater :: Comparison x y

lift :: Comparison x y -> Comparison (f x) (f y)
lift = \case
  Lesser  -> Lesser
  Equal   -> Equal
  Greater -> Greater

lift2 :: Comparison x y -> Comparison z w -> Comparison (f x z) (f y w)
lift2 a b = case (a, b) of
  (Lesser , _      ) -> Lesser
  (Equal  , Lesser ) -> Lesser
  (Equal  , Equal  ) -> Equal
  (Equal  , Greater) -> Greater
  (Greater, _      ) -> Greater

class Signature (sig :: k -> Type) where
  match :: sig x -> sig y -> Comparison x y

-- data Any s f where
--   Any :: forall t s f. Exp (f t) => s t -> f t -> Any s f

type Any' = Any1 ExpSig Const ()

-- instance Signature s => Eq (Any s f) where
--   Any s x == Any t y = case match s t of
--     Equal -> x == y
--     _     -> False

-- instance Signature s => Ord (Any s c) where
--   Any s x `compare` Any t y = case match s t of
--     Equal   -> x `compare` y
--     Lesser  -> LT
--     Greater -> GT

-- instance Signature s => Show (Any s c) where
--   showsPrec p (Any _ x) r
--     | p > 10 = "(Any " ++ showsPrec 11 x ")" ++ r
--     | otherwise = "Any " ++ showsPrec 11 x r

data Any1 s f a where
  Any1 :: forall t s f a. Fun (f t) => s t -> f t a -> Any1 s f a

instance (Signature s, Eq a) => Eq (Any1 s f a) where
  (==) = liftEq (==)

instance Signature s => Eq1 (Any1 s f) where
  liftEq eq (Any1 s x) (Any1 t y) = case match s t of
    Equal -> liftEq eq x y
    _     -> False

instance (Signature s, Ord a) => Ord (Any1 s f a) where
  compare = liftCompare compare

instance Signature s => Ord1 (Any1 s f) where
  liftCompare cmp (Any1 s x) (Any1 t y) = case match s t of
    Equal   -> liftCompare cmp x y
    Lesser  -> LT
    Greater -> GT

instance (Show a, Signature s) => Show (Any1 s f a) where
  showsPrec p x = liftShowsPrec showsPrec showList p x

instance Signature s => Show1 (Any1 s f) where
  liftShowsPrec sp sl p (Any1 _ x) r
    | p > 10 = "(Any1 " ++ liftShowsPrec sp sl 11 x ")" ++ r
    | otherwise = "Any1 " ++ liftShowsPrec sp sl 11 x r

instance Functor (Any1 s f) where
  fmap f (Any1 s x) = Any1 s (fmap f x)

instance Foldable (Any1 s f) where
  foldMap f (Any1 _ x) = foldMap f x

instance Traversable (Any1 s f) where
  traverse f (Any1 s x) = Any1 s <$> traverse f x

---- Expressions ----

type Exp t = Each [Eq, Ord, Show] t

data ExpSig t where
  Nat :: ExpSig Natural
  Str :: ExpSig String

instance Signature ExpSig where
  match :: ExpSig t -> ExpSig u -> Comparison t u
  match Nat Nat = Equal
  match Str Str = Equal
  match Nat Str = Lesser
  match Str Nat = Greater

-- type AnyExp = Any' ExpSig (Compose Identity)

---- Functors ----

type Fun f = Container f

type Container f =
  Each [Functor, Foldable, Traversable, Eq1, Ord1, Show1, Pretty] f

data FunSig f where
  I :: FunSig Identity
  K :: Exp t => ExpSig t -> FunSig (Const t)
  P :: (Fun f, Fun g) => FunSig f -> FunSig g -> FunSig (Product f g)
  S :: (Fun f, Fun g) => FunSig f -> FunSig g -> FunSig (Sum f g)
  L :: Fun f => FunSig f -> FunSig (Compose [] f)

instance Signature FunSig where
  match :: FunSig f -> FunSig g -> Comparison f g
  match s t = case (s, t) of
    (I, I) -> Equal
    (K k, K l)
      | Equal <- match k l
      -> Equal
      | otherwise -> lift $ match k l
    (P s1 s2, P t1 t2)
      | Equal <- match s1 t1
      , Equal <- match s2 t2
      -> Equal
      | otherwise -> lift2 (match s1 t1) (match s2 t2)
    (S s1 s2, S t1 t2)
      | Equal <- match s1 t1
      , Equal <- match s2 t2
      -> Equal
      | otherwise -> lift2 (match s1 t1) (match s2 t2)
    (L s1, L t1)
      | Equal <- match s1 t1
      -> Equal
      | otherwise -> lift $ match s1 t1
    (I , _) -> Lesser
    (K _, I) -> Greater
    (K _, _) -> Lesser
    (P {}, I) -> Greater
    (P {}, K _) -> Greater
    (P {}, _) -> Lesser
    (S {}, L _) -> Lesser
    (S {}, _) -> Greater
    (L _, _) -> Greater

  -- type Constraints =
  --   [Functor, Foldable, Traversable, Eq1, Ord1, Show1, Pretty]

-- TODO: maybe some newtype other than Compose Identity?
type AnyFun = Any1 FunSig (Compose Identity)

pattern AnyFun :: () => Fun (Compose Identity t) => FunSig t -> t a -> AnyFun a
pattern AnyFun s x = Any1 s (Compose (Identity x))

instance Pretty AnyFun where
  pretty p (Any1 _ x) = pretty p x

data CtxSig f where
  N :: CtxSig (Const ())
  E :: String -> FunSig f -> CtxSig g -> CtxSig (Product f g)

instance Signature CtxSig where
  match N N = Equal
  match (E s x xs) (E t y ys) = case compare s t of
    LT -> Lesser
    EQ -> lift2 (match x y) (match xs ys)
    GT -> Greater
  match N _ = Lesser
  match _ _ = Greater

type Context = Any1 CtxSig (Compose Identity)

pattern Context :: () => Fun (Compose Identity t) =>
  CtxSig t -> t a -> Context a
pattern Context s x = Any1 s (Compose (Identity x))

-- instance Pretty Context where
--   pretty _ ()

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

-- >>> show example
-- "{e = Any1 (Compose (Identity (InL (Const \"Error\")))), x = Any1 (Compose (Identity (Identity 4))), xs = Any1 (Compose (Identity (Compose [Identity 1,Identity 2,Identity 3])))}"

ex2 :: AnyFun Int
ex2 = AnyFun (P (S (S I (K Str)) I) (L I))
  $ Pair (InL (InR "Hello")) (Compose [1, 2, 3])

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
