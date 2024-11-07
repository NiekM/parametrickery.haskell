module Language.Expr
  ( Expr
    ( ..
    , Value
    , Unit
    , Apps
    , Lams
    , Case, If
    , Bool
    , Ordering
    , Nil, Cons, List
    , Zero, Succ, Nat
    )
  , Lit(..)
  , Program
  , Term
  , Value
  , holes
  , accept
  , norm
  , asProgram
  , tuple
  , lets
  ) where

import Prelude hiding (Enum(..))

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Foldable

import Data.Tree

import Unsafe.Coerce qualified as Unsafe

import Base

newtype Lit = MkInt Int
  deriving stock (Eq, Ord, Show)

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
  Hole :: h -> Expr l h

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

instance Applicative (Expr l) where
  pure :: a -> Expr l a
  pure = Hole

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
  Hole e -> e

instance Project (Expr l h) where
  projections = \case
    Tuple xs -> xs
    x -> [x]

holes :: Expr l h -> [h]
holes = toList

tuple :: [Expr l h] -> Expr l h
tuple [x] = x
tuple xs = Tuple xs

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
    Apps (Var "fold") [node, leaf, Tree t] -> norm ctx $
      foldTree (\l y r -> Apps node [l, y, r]) (Apps leaf . projections) t
    Apps (Var "fold") [succ, zero, Nat n] -> norm ctx $
      applyN n (App succ) zero
    Apps (Var "map") [g, List xs] -> List $ map (norm ctx . App g) xs
    Apps (Var "filter") [p, List xs] -> List $
      filter (fromMaybe False . unBool . norm ctx . App p) xs
    Apps (Var "eq" ) [Value a, Value b] -> Bool (a == b)
    Apps (Var "cmp") [Value a, Value b] -> Ordering (compare a b)
    e -> e
  Prj i x -> case norm ctx x of
    Tuple xs -> norm ctx $ xs !! fromIntegral i
    y -> Prj i y
  Elim xs -> Elim $ map (norm ctx <$>) xs
  Hole h -> Hole h

-- Smart constructors

asProgram :: Expr l h -> Program h
asProgram = Unsafe.unsafeCoerce

-- * Values

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

pattern Value :: Value -> Expr l h
pattern Value v <- (toValue -> Just v)
  where Value v = fromValue v

fromValue :: Value -> Expr l h
fromValue = \case
  Hole v -> absurd v
  e -> Unsafe.unsafeCoerce e

-- * Units

pattern Unit :: Expr l h
pattern Unit = Tuple []

-- * Applications

unApps :: Expr l h -> (Expr l h, [Expr l h])
unApps = \case
  App f e -> second (++ [e]) $ unApps f
  e -> (e, [])

{-# COMPLETE Apps #-}
pattern Apps :: Program h -> [Program h] -> Program h
pattern Apps f xs <- (unApps -> (f, xs))
  where Apps f xs = foldl' App f xs

-- * Lambdas

unLams :: Expr l h -> ([Name], Expr l h)
unLams = \case
  Lam x e -> first (x:) $ unLams e
  e -> ([], e)

{-# COMPLETE Lams #-}
pattern Lams :: [Name] -> Program h -> Program h
pattern Lams xs e <- (unLams -> (xs, e))
  where Lams xs e = foldr Lam e xs

lets :: [Named (Program h)] -> Program h -> Program h
lets bindings body = Apps (Lams vars body) args
  where
    vars = map (.name)  bindings
    args = map (.value) bindings

-- * Pattern matching

pattern Case :: () => (l ~ True) => Expr l h -> [(Name, Expr l h)] -> Expr l h
pattern Case e xs = App (Elim xs) e

pattern If :: () => (l ~ True) => Expr l h -> Expr l h -> Expr l h -> Expr l h
pattern If b t f = Case b [("True", t), ("False", f)]

-- * Lists

pattern Nil :: Expr l h
pattern Nil = Ctr "[]" Unit

pattern Cons :: Expr l h -> Expr l h -> Expr l h
pattern Cons x xs = Ctr ":" (Tuple [x, xs])

unList :: Expr l h -> Maybe [Expr l h]
unList = \case
  Nil -> Just []
  Cons x xs -> (x:) <$> unList xs
  _ -> Nothing

pattern List :: [Expr l h] -> Expr l h
pattern List xs <- (unList -> Just xs)
  where List xs = foldr Cons Nil xs

-- * Trees

unTree :: Expr l h -> Maybe (Tree (Expr l h) (Expr l h))
unTree = \case
  Ctr "Leaf" x -> Just $ Leaf x
  Ctr "Node" (Tuple [l, x, r]) -> Node <$> unTree l <*> pure x <*> unTree r
  _ -> Nothing

pattern Tree :: Tree (Expr l h) (Expr l h) -> Expr l h
pattern Tree t <- (unTree -> Just t)

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

-- * Bools

unBool :: Expr l h -> Maybe Bool
unBool = \case
  Ctr "True"  Unit -> Just True
  Ctr "False" Unit -> Just False
  _ -> Nothing

pattern Bool :: Bool -> Expr l h
pattern Bool b <- (unBool -> Just b)
  where Bool b = Ctr (fromString $ show b) Unit

-- * Orderings

unOrdering :: Expr l h -> Maybe Ordering
unOrdering = \case
  Ctr "LT" Unit -> Just LT
  Ctr "EQ" Unit -> Just EQ
  Ctr "GT" Unit -> Just GT
  _ -> Nothing

pattern Ordering :: Ordering -> Expr l h
pattern Ordering o <- (unOrdering -> Just o)
  where Ordering o = Ctr (fromString $ show o) Unit