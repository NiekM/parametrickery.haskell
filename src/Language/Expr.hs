module Language.Expr where

import Prelude hiding (Enum(..))

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Foldable

import Base

newtype Lit = MkInt Int
  deriving stock (Eq, Ord, Show)

-- Used for pretty printing
newtype Hole h = MkHole { hole :: h }
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

data Expr (l :: Bool) h where
  -- Constructions
  Tuple :: [Expr l h] -> Expr l h
  Ctr :: Name -> Expr l h -> Expr l h
  Lit :: Lit -> Expr l h
  -- Lambda expressions
  Var :: Name -> Program h
  Lam :: Name -> Program h -> Program h
  App :: Program h -> Program h -> Program h
  -- Deconstructions
  Prj :: Nat -> Program h -> Program h
  Elim :: [(Name, Program h)] -> Program h
  -- Holes
  Hole :: Hole h -> Expr l h

-- TODO: The derived Ord instance uses comparison of Text to compare
-- constructors, but this messes with the ordering of examples. Perhaps a
-- better solution would be to just use a natural number internally for
-- constructors and only retrieving the constructor name during pretty
-- printing.
deriving stock instance Eq   h => Eq   (Expr l h)
deriving stock instance Ord  h => Ord  (Expr l h)
deriving stock instance Show h => Show (Expr l h)

deriving stock instance Functor     (Expr l)
deriving stock instance Foldable    (Expr l)
deriving stock instance Traversable (Expr l)

type Program = Expr True
type Term    = Expr False
type Value   = Term Void

pattern Unit :: Expr l h
pattern Unit = Tuple []

instance Applicative (Expr l) where
  pure :: a -> Expr l a
  pure = Hole . MkHole

  liftA2 :: (a -> b -> c) -> Expr l a -> Expr l b -> Expr l c
  liftA2 f x y = x >>= \a -> y >>= \b -> pure $ f a b

instance Monad (Expr l) where
  (>>=) :: Expr l a -> (a -> Expr l b) -> Expr l b
  x >>= f = accept $ fmap f x

-- Accept the hole fillings (i.e. join)
accept :: Expr l (Expr l h) -> Expr l h
accept = \case
  Tuple xs -> Tuple (map accept xs)
  Ctr c x -> Ctr c (accept x)
  Lit l -> Lit l
  Var v -> Var v
  Lam v x -> Lam v (accept x)
  App f x -> App (accept f) (accept x)
  Prj i x -> Prj i (accept x)
  Elim xs -> Elim (map (fmap accept) xs)
  Hole e -> e.hole

holes :: Expr l h -> [h]
holes = toList

-- * Lists

pattern Nil :: Expr l h
pattern Nil = Ctr "Nil" Unit

pattern Cons :: Expr l h -> Expr l h -> Expr l h
pattern Cons x xs = Ctr "Cons" (Tuple [x, xs])

unList :: Expr l h -> Maybe [Expr l h]
unList = \case
  Nil -> Just []
  Cons x xs -> (x:) <$> unList xs
  _ -> Nothing

pattern List :: [Expr l h] -> Expr l h
pattern List xs <- (unList -> Just xs)
  where List xs = foldr Cons Nil xs

-- * Nats

pattern Zero :: Expr l h
pattern Zero = Ctr "Zero" Unit

pattern Succ :: Expr l h -> Expr l h
pattern Succ n = Ctr "Succ" n

unNat :: Expr l h -> Maybe Nat
unNat = \case
  Zero -> Just 0
  Succ n -> (1+) <$> unNat n
  _ -> Nothing

applyN :: Nat -> (a -> a) -> a -> a
applyN n f = foldr (.) id $ replicate (fromIntegral n) f

pattern Nat :: Nat -> Expr l h
pattern Nat n <- (unNat -> Just n)
  where Nat n = applyN n Succ Zero

fromTerm :: Term h -> Program h
fromTerm = \case
  Tuple xs -> Tuple (map fromTerm xs)
  Ctr c x -> Ctr c (fromTerm x)
  Lit i -> Lit i
  Hole h -> Hole h

unLams :: Expr l h -> ([Name], Expr l h)
unLams = \case
  Lam x e -> first (x:) $ unLams e
  e -> ([], e)

{-# COMPLETE Lams #-}
pattern Lams :: [Name] -> Expr l h -> Expr l h
pattern Lams xs e <- (unLams -> (xs, e))

lams :: [Name] -> Program h -> Program h
lams xs e = foldr Lam e xs

unApps :: Expr l h -> (Expr l h, [Expr l h])
unApps = \case
  App f e -> second (++ [e]) $ unApps f
  e -> (e, [])

{-# COMPLETE Apps #-}
pattern Apps :: Program h -> [Program h] -> Program h
pattern Apps f xs <- (unApps -> (f, xs))
  where Apps f xs = foldl' App f xs

tuple :: [Expr l h] -> Expr l h
tuple [x] = x
tuple xs = Tuple xs

pattern Case :: Program h -> [(Name, Program h)] -> Program h
pattern Case e xs = App (Elim xs) e

lets :: [Named (Program h)] -> Program h -> Program h
lets bindings body = Apps (lams vars body) args
  where
    vars = map (.name)  bindings
    args = map (.value) bindings

pattern IfThenElse :: Program h -> Program h -> Program h -> Program h
pattern IfThenElse b t f = Case b [("True", t), ("False", f)]

instance Project (Expr l h) where
  projections = \case
    Tuple xs -> xs
    x -> [x]

bool :: Bool -> Expr l h
bool False = Ctr "False" Unit
bool True  = Ctr "True"  Unit

ordering :: Ordering -> Expr l h
ordering LT = Ctr "LT" Unit
ordering EQ = Ctr "EQ" Unit
ordering GT = Ctr "GT" Unit

toBool :: Expr l h -> Maybe Bool
toBool (Ctr "True"  Unit) = Just True
toBool (Ctr "False" Unit) = Just False
toBool _ = Nothing

norm :: Map Name (Program h) -> Program h -> Program h
norm ctx = \case
  Tuple xs -> Tuple $ map (norm ctx) xs
  Ctr c x -> Ctr c $ norm ctx x
  Lit i -> Lit i
  Var v -> case Map.lookup v ctx of
    Just x -> x
    Nothing -> Var v
  Lam v x -> case norm ctx x of
    App f (Var w) | v == w -> f
    y -> Lam v y
  App f x -> case App (norm ctx f) (norm ctx x) of
    App (Lam v e) y -> norm (Map.insert v y ctx) e
    Case (Ctr c e) xs -> norm ctx $
      Apps (Maybe.fromJust $ List.lookup c xs) (projections e)
    Apps (Var "fold") [cons, nil, List xs] -> norm ctx $
      foldr (\y r -> Apps cons [y, r]) nil xs
    Apps (Var "fold") [succ, zero, Nat n] -> norm ctx $
      applyN n (App succ) zero
    Apps (Var "map") [g, List xs] -> List $ map (norm ctx . App g) xs
    Apps (Var "filter") [p, List xs] -> List $
      filter (fromMaybe False . toBool . norm ctx . App p) xs
    Apps (Var "eq") [a, b]
      | Just aa <- toValue a
      , Just bb <- toValue b -> bool (aa == bb)
    Apps (Var "cmp") [a, b]
      | Just aa <- toValue a
      , Just bb <- toValue b -> ordering (compare aa bb)
    e -> e
  Prj i x -> case norm ctx x of
    Tuple xs -> norm ctx $ xs !! fromIntegral i
    y -> Prj i y
  Elim xs -> Elim $ map (norm ctx <$>) xs
  Hole h -> Hole h

-- NOTE: these form a prism
toValue :: Expr l h -> Maybe Value
toValue = \case
  Tuple xs -> Tuple <$> traverse toValue xs
  Ctr c x -> Ctr c <$> toValue x
  Lit i -> Just $ Lit i
  Var _ -> Nothing
  Lam _ _ -> Nothing
  App _ _ -> Nothing
  Prj _ _ -> Nothing
  Elim _ -> Nothing
  Hole _ -> Nothing

fromValue :: Value -> Expr l h
fromValue = \case
  Tuple xs -> Tuple $ map fromValue xs
  Ctr c x -> Ctr c $ fromValue x
  Lit i -> Lit i
  Hole (MkHole v) -> absurd v

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { inputs :: [Value]
  , output :: Value
  } deriving stock (Eq, Ord, Show)

instance Project Example where
  projections (Example ins out) = Example ins <$> projections out
