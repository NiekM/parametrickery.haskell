module Language.Expr where

import Data.Foldable

import Base

newtype Lit = MkInt Int
  deriving stock (Eq, Ord, Show)

-- Used for pretty printing
newtype Hole h = MkHole { hole :: h }
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

data Expr h where
  Tuple :: [Expr h] -> Expr h
  Ctr  :: Text -> Expr h -> Expr h
  Lit  :: Lit -> Expr h
  Hole :: Hole h -> Expr h
  -- TODO: The derived Ord instance uses comparison of Text to compare
  -- constructors, but this messes with the ordering of examples. Perhaps a
  -- better solution would be to just use a natural number internally for
  -- constructors and only retrieving the constructor name during pretty
  -- printing.
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

pattern Unit :: Expr h
pattern Unit = Tuple []

pattern Nil :: Expr h
pattern Nil = Ctr "Nil" Unit

pattern Cons :: Expr h -> Expr h -> Expr h
pattern Cons x xs = Ctr "Cons" (Tuple [x, xs])

type Term = Expr Void

instance Applicative Expr where
  pure :: a -> Expr a
  pure = Hole . MkHole

  liftA2 :: (a -> b -> c) -> Expr a -> Expr b -> Expr c
  liftA2 f x y = x >>= \a -> y >>= \b -> pure $ f a b

instance Monad Expr where
  (>>=) :: Expr a -> (a -> Expr b) -> Expr b
  x >>= f = accept $ fmap f x

-- Accept the hole fillings (i.e. join)
accept :: Expr (Expr h) -> Expr h
accept = \case
  Tuple xs -> Tuple (map accept xs)
  Ctr c x -> Ctr c (accept x)
  Lit l -> Lit l
  Hole e -> e.hole

holes :: Expr h -> [h]
holes = toList

mkList :: [Expr h] -> Expr h
mkList = foldr Cons Nil

unList :: Expr h -> Maybe [Expr h]
unList = \case
  Nil -> Just []
  Cons x xs -> (x:) <$> unList xs
  _ -> Nothing

pattern List :: [Expr h] -> Expr h
pattern List xs <- (unList -> Just xs)
  where List xs = mkList xs

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { inputs :: [Term]
  , output :: Term
  } deriving stock (Eq, Ord, Show)
