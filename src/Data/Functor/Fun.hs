{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Functor.Fun where

import Data.String (IsString(..))
import Data.List       qualified as List
import Data.Map.Strict qualified as Map

import Base

------ Expressions ------

data Exp t where
  Nat :: Natural -> Exp Natural
  Str :: String  -> Exp String

instance Eq (Exp t) where
  Nat n == Nat m = n == m
  Str s == Str t = s == t

instance Ord (Exp t) where
  Nat n `compare` Nat m = n `compare` m
  Str s `compare` Str t = s `compare` t

instance Show (Exp t) where
  show = \case
    Nat n -> show n
    Str s -> show s

instance Num (Exp Natural) where
  Nat n + Nat m = Nat (n + m)
  Nat n * Nat m = Nat (n * m)
  Nat n - Nat m = Nat (n - m)
  abs (Nat n) = Nat (abs n)
  signum (Nat n) = Nat (signum n)
  fromInteger = Nat . fromInteger

instance IsString (Exp String) where
  fromString = Str

------ Functors ------

data Fun f a where
  I :: a -> Fun Identity a
  K :: Exp k -> Fun (Const k) a
  P :: Fun f a -> Fun g a -> Fun (Product f g) a
  A :: Fun f a -> Fun (Sum f g) a
  B :: Fun g a -> Fun (Sum f g) a
  L :: [Fun f a] -> Fun (Compose [] f) a

instance Functor (Fun f) where
  fmap f = \case
    I x   -> I (f x)
    K k   -> K k
    P x y -> P (fmap f x) (fmap f y)
    A x   -> A (fmap f x)
    B y   -> B (fmap f y)
    L xs  -> L (fmap (fmap f) xs)

instance Foldable (Fun f) where
  foldMap f = \case
    I x   -> f x
    K _   -> mempty
    P x y -> foldMap f x <> foldMap f y
    A x   -> foldMap f x
    B y   -> foldMap f y
    L xs  -> foldMap (foldMap f) xs

instance Traversable (Fun f) where
  traverse f = \case
    I x   -> fmap I (f x)
    K k   -> pure (K k)
    P x y -> P <$> traverse f x <*> traverse f y
    A x   -> A <$> traverse f x
    B y   -> B <$> traverse f y
    L xs  -> L <$> traverse (traverse f) xs

instance Eq a => Eq (Fun f a) where
  (==) = liftEq (==)

instance Eq1 (Fun f) where
  liftEq = liftEq'

instance Ord a => Ord (Fun f a) where
  compare = liftCompare compare

instance Ord1 (Fun f) where
  liftCompare = liftCmp'

instance Show a => Show (Fun f a) where
  show x = liftShowsPrec showsPrec showList 0 x ""

instance Show1 (Fun f) where
  liftShowsPrec sp sl p = \case
    I x -> sp p x
    K k -> showsPrec p k
    P x y -> liftShowsPrec2
      (liftShowsPrec sp sl) (liftShowList sp sl)
      (liftShowsPrec sp sl) (liftShowList sp sl)
      p (x, y)
    A x -> liftShowsPrec2
      (liftShowsPrec sp sl) (liftShowList sp sl)
      undefined undefined
      p (Left x)
    B y -> liftShowsPrec2
      undefined undefined
      (liftShowsPrec sp sl) (liftShowList sp sl)
      p (Right y)
    L xs -> liftShowsPrec
      (liftShowsPrec sp sl) (liftShowList sp sl) p xs

instance Num a => Num (Fun Identity a) where
  I n + I m = I (n + m)
  I n * I m = I (n * m)
  I n - I m = I (n - m)
  abs (I n) = I (abs n)
  signum (I n) = I (signum n)
  fromInteger = I . fromInteger

instance IsString a => IsString (Fun Identity a) where
  fromString = I . fromString

instance Num (Fun (Const Natural) a) where
  K n + K m = K (n + m)
  K n * K m = K (n * m)
  K n - K m = K (n - m)
  abs (K n) = K (abs n)
  signum (K n) = K (signum n)
  fromInteger = K . fromInteger

instance IsString (Fun (Const String) a) where
  fromString = K . fromString

------ Evaluation ------

evalExp :: Exp t -> t
evalExp = \case
  Nat n -> n
  Str s -> s

evalFun :: Fun f a -> f a
evalFun = \case
  I x   -> Identity x
  K k   -> Const (evalExp k)
  P x y -> Pair (evalFun x) (evalFun y)
  A x   -> InL (evalFun x)
  B y   -> InR (evalFun y)
  L xs  -> Compose (map evalFun xs)

------ Any ------

data AnyFun a = forall f. AnyFun (Fun f a)

instance Functor AnyFun where
  fmap f (AnyFun x) = AnyFun (fmap f x)

instance Foldable AnyFun where
  foldMap f (AnyFun x) = foldMap f x

instance Traversable AnyFun where
  traverse f (AnyFun x) = AnyFun <$> traverse f x

instance Eq a => Eq (AnyFun a) where
  (==) = liftEq (==)

instance Eq1 AnyFun where
  liftEq eq (AnyFun x) (AnyFun y) = liftEq' eq x y

instance Ord a => Ord (AnyFun a) where
  compare = liftCompare compare

instance Ord1 AnyFun where
  liftCompare cmp (AnyFun x) (AnyFun y) = liftCmp' cmp x y

instance Show a => Show (AnyFun a) where
  show x = liftShowsPrec showsPrec showList 0 x ""

instance Show1 AnyFun where
  liftShowsPrec sp sl p (AnyFun x) =
    liftShowsPrec sp sl p x

liftEq' :: (a -> b -> Bool) -> Fun f a -> Fun g b -> Bool
liftEq' eq a b = case (a, b) of
  (I x  , I y  ) -> eq x y
  (K k  , K l  ) -> AnyExp k == AnyExp l
  (P x y, P z w) -> liftEq' eq x z && liftEq' eq y w
  (A x  , A y  ) -> liftEq' eq x y
  (B x  , B y  ) -> liftEq' eq x y
  (L xs , L ys ) -> liftEq (liftEq' eq) xs ys
  _ -> False

liftCmp' :: (a -> b -> Ordering) -> Fun f a -> Fun g b -> Ordering
liftCmp' cmp a b = case (a, b) of
  (I x  , I y  ) -> cmp x y
  (K k  , K l  ) -> AnyExp k `compare` AnyExp l
  (P x y, P z w) -> liftCmp' cmp x z <> liftCmp' cmp y w
  (A x  , A y  ) -> liftCmp' cmp x y
  (B x  , B y  ) -> liftCmp' cmp x y
  (L xs , L ys ) -> liftCompare (liftCmp' cmp) xs ys
  (_    , _    ) -> compare (ctrIndex a) (ctrIndex b)
  where
    ctrIndex :: Fun f a -> Natural
    ctrIndex = \case
      I _ -> 0; K _ -> 1; P _ _ -> 2
      A _ -> 3; B _ -> 4; L _   -> 5

data AnyExp = forall t. AnyExp (Exp t)

instance Eq AnyExp where
  AnyExp x == AnyExp y = case (x, y) of
    (Nat n, Nat m) -> n == m
    (Str s, Str t) -> s == t
    _ -> False

instance Ord AnyExp where
  AnyExp x `compare` AnyExp y = case (x, y) of
    (Nat n, Nat m) -> compare n m
    (Str s, Str t) -> compare s t
    _ -> compare (ctrIndex x) (ctrIndex y)
      where
        ctrIndex :: Exp t -> Natural
        ctrIndex = \case Nat _ -> 0; Str _ -> 1

------ Contexts ------

newtype Ctx a = Ctx (Map String (AnyFun a))

instance Functor Ctx where
  fmap f (Ctx m) = Ctx $ fmap (fmap f) m

instance Foldable Ctx where
  foldMap f (Ctx m) = foldMap (foldMap f) m

instance Traversable Ctx where
  traverse f (Ctx m) = Ctx <$> traverse (traverse f) m

instance Eq a => Eq (Ctx a) where
  (==) = liftEq (==)

instance Eq1 Ctx where
  liftEq eq (Ctx m) (Ctx n) =
    liftEq (\(AnyFun a) (AnyFun b) -> liftEq' eq a b) m n

instance Ord a => Ord (Ctx a) where
  compare = liftCompare compare

instance Ord1 Ctx where
  liftCompare cmp (Ctx m) (Ctx n) =
    liftCompare (\(AnyFun a) (AnyFun b) -> liftCmp' cmp a b) m n

instance Show a => Show (Ctx a) where
  show (Ctx c) =
    "{" ++ List.intercalate ", " (showMap <$> Map.assocs c) ++ "}"
    where showMap (k, v) = k ++ " = " ++ show v

------ Examples ------

getList :: AnyFun a -> [AnyFun a]
getList = \case
  AnyFun (L xs) -> AnyFun <$> xs
  _ -> []

example :: Ctx Int
example = Ctx $ Map.fromList
  [ ("xs", AnyFun @_ @(Compose [] Identity) $ L [1, 2, 3])
  , ("x", AnyFun @_ @Identity 4)
  , ("e", AnyFun @_ @(Sum (Const String) Identity) $ A "Error")
  ]

-- >>> example
-- {e = Left "Error", x = 4, xs = [1,2,3]}

ex2 :: AnyFun Int
ex2 = AnyFun $ P
  (A @_ @_ @Identity (B @(Const String) @_ @Identity "Hello"))
  (L @Identity [1,2,3])

-- >>> ex2
-- (Left (Right "Hello"),[1,2,3])


{-

Using functions such as `listArguments` we can check if a refinement is possible
(in this case, introducing foldr).
TODO: create functions for restricting the context to a subset.

-}

extractEach :: Ord k => Map k v -> [(k, v, Map k v)]
extractEach m = Map.assocs m <&> \(k, v) -> (k, v, Map.delete k m)

listArguments :: Ctx a -> [(String, [AnyFun a], Ctx a)]
listArguments (Ctx ctx) = extractEach ctx >>= \(s, f, ctx') -> case f of
  AnyFun (L xs) -> [(s, AnyFun <$> xs, Ctx ctx')]
  _ -> []

