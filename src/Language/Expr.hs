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
  Prj i x -> Prj i (accept x)
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
lams = flip $ foldr Lam

unApps :: Expr l h -> (Expr l h, [Expr l h])
unApps = \case
  App f e -> second (++ [e]) $ unApps f
  e -> (e, [])

{-# COMPLETE Apps #-}
pattern Apps :: Expr l h -> [Expr l h] -> Expr l h
pattern Apps f xs <- (unApps -> (f, xs))

apps :: Program h -> [Program h] -> Program h
apps = foldl' App

tuple :: [Expr l h] -> Expr l h
tuple [x] = x
tuple xs = Tuple xs

norm :: Map Name (Program h) -> Program h -> Program h
norm ctx e = case e of
  Tuple xs -> Tuple $ map (norm ctx) xs
  Ctr c x -> Ctr c $ norm ctx x
  Lit i -> Lit i
  Var v -> case Map.lookup v ctx of
    Just x -> x
    Nothing -> Var v
  Lam v x -> case norm ctx x of
    App f (Var w) | v == w -> f
    y -> Lam v y
  App f x -> case norm ctx f of
    Lam v y -> norm (Map.insert v (norm ctx x) ctx) y
    g -> App g $ norm ctx x
  Prj i x -> case norm ctx x of
    Tuple xs -> xs !! fromIntegral i
    y -> Prj i y
  Hole h -> Hole h

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { inputs :: [Value]
  , output :: Value
  } deriving stock (Eq, Ord, Show)
