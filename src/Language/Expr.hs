module Language.Expr where

import Data.Map qualified as Map
import Data.Foldable

import Base

newtype Lit = MkInt Int
  deriving stock (Eq, Ord, Show)

-- Used for pretty printing
newtype Hole h = MkHole { hole :: h }
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

data Expr (l :: Bool) h where
  -- Data expressions
  Tuple :: [Expr l h] -> Expr l h
  Ctr :: Text -> Expr l h -> Expr l h
  Lit :: Lit -> Expr l h
  -- Lambda expressions
  Var :: Text -> Program h
  Lam :: Text -> Program h -> Program h
  App :: Program h -> Program h -> Program h
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

pattern Nil :: Expr l h
pattern Nil = Ctr "Nil" Unit

pattern Cons :: Expr l h -> Expr l h -> Expr l h
pattern Cons x xs = Ctr "Cons" (Tuple [x, xs])

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
  Hole e -> e.hole

holes :: Expr l h -> [h]
holes = toList

mkList :: [Expr l h] -> Expr l h
mkList = foldr Cons Nil

unList :: Expr l h -> Maybe [Expr l h]
unList = \case
  Nil -> Just []
  Cons x xs -> (x:) <$> unList xs
  _ -> Nothing

pattern List :: [Expr l h] -> Expr l h
pattern List xs <- (unList -> Just xs)
  where List xs = mkList xs

apps :: Program h -> [Program h] -> Program h
apps = foldl' App

eval :: Map Text (Program h) -> Program h -> Maybe (Program h)
eval ctx = \case
  Tuple xs -> Tuple <$> mapM (eval ctx) xs
  Ctr c x -> Ctr c <$> eval ctx x
  Lit i -> Just $ Lit i
  Var v -> Map.lookup v ctx >>= eval ctx
  Lam v x -> Just $ Lam v x
  App f x -> eval ctx f >>= \case
    Lam v y -> eval (Map.insert v y ctx) x
    y -> Just $ App f y
  Hole h -> Just $ Hole h

toValue :: Expr l h -> Maybe Value
toValue = \case
  Tuple xs -> Tuple <$> mapM toValue xs
  Ctr c x -> Ctr c <$> toValue x
  Lit i -> Just $ Lit i
  _ -> Nothing

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { inputs :: [Value]
  , output :: Value
  } deriving stock (Eq, Ord, Show)
