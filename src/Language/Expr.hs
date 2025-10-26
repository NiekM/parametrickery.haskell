{-# LANGUAGE TypeAbstractions #-}
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
  , freeVars
  , normalize
  , asProgram
  , toValue
  , tuple
  , lets
  , compareVal
  ) where

import Prelude hiding (Enum(..), error)

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Foldable

import Data.Tango.List.List as LL
import Data.Tango.List.Nat  as LN
import Data.Tree.Binary

import Unsafe.Coerce qualified as Unsafe

import Base

newtype Lit = MkInt Int
  deriving stock (Eq, Ord, Show)

data Expr (l :: Bool) h where
  -- Constructions
  Tuple :: [Expr l h] -> Expr l h
  -- TODO: use natural numbers for constructors to describe the ordering non-lexicographically
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

freeVars :: Program h -> Set Name
freeVars = \case
  Tuple xs -> foldMap freeVars xs
  Ctr _ x -> freeVars x
  Lit _ -> Set.empty
  Var v -> Set.singleton v
  Lam v x -> Set.filter (/= v) $ freeVars x
  App f x -> freeVars f <> freeVars x
  Prj _ x -> freeVars x
  Elim xs -> foldMap (freeVars . snd) xs
  Hole _ -> Set.empty

tuple :: [Expr l h] -> Expr l h
tuple [x] = x
tuple xs = Tuple xs

normalize :: Expr l h -> Expr l h
normalize = norm mempty

paraNat :: ((Nat, b) -> b) -> b -> Nat -> b
paraNat _ e 0 = e
paraNat g e n = g (n - 1, paraNat g e (n - 1))

paraList :: (a -> ([a], b) -> b) -> b -> [a] -> b
paraList _ e [] = e
paraList g e (y:ys) = g y (ys, paraList g e ys)

-- TODO: define comparison for other values (not using lexicographical ordering of constructors)
compareVal :: Value -> Value -> Ordering
compareVal (Lit i) (Lit j) = compare i j
compareVal (Nat n) (Nat m) = compare n m
compareVal _ _ = error "comparison between non-literals undefined"

norm :: Map Name (Expr l h) -> Expr l h -> Expr l h
norm @_ @h ctx = \case
  Tuple xs -> Tuple $ map (norm ctx) xs
  Ctr c x -> Ctr c $ norm ctx x
  Lit i -> Lit i
  Var v -> case Map.lookup v ctx of
    Just x -> x
    Nothing -> Var v
  Lam v x -> case norm ctx x of
    App f (Var z) | v == z, Set.notMember z (freeVars f) -> f
    y -> Lam v y
  App f x -> case App (norm ctx f) (norm ctx x) of
    App (Lam v e) y -> norm (Map.insert v y ctx) e
    Case (Ctr c e) xs -> case List.lookup c xs of
      Nothing -> error $ "Unknown constructor " <> show c
      Just r -> norm ctx $ App r (norm ctx e)
    Apps (Var "cata") [alg, arg@Ctr{}] -> norm ctx $ appCata alg arg
    Apps (Var "para") [alg, arg@Ctr{}] -> norm ctx $ appPara alg arg
    Apps (Var "map") [g, List xs] -> List $ map (norm ctx . App g) xs
    Apps (Var "filter") [p, List xs] -> List $
      filter (fromMaybe False . unBool . norm ctx . App p) xs
    Apps (Var "tango") [List xs, List ys] -> mkTangoLL $ LL.tango xs ys
    Apps (Var "tango") [List xs, Nat n] -> mkTangoLN $ LN.tango xs n
    Apps (Var "eq" ) [Value a, Value b] -> Bool (a == b)
    Apps (Var "cmp") [Value a, Value b] -> Ordering (compareVal a b)
    e -> e
  Prj i x -> case norm ctx x of
    Tuple xs -> norm ctx $ xs !! fromIntegral i
    y -> Prj i y
  Elim xs -> Elim $ map (norm ctx <$>) xs
  Hole h -> Hole h

  where
    appCata :: Program h -> Program h -> Program h
    appCata alg = \case
      List xs -> foldr (\y r -> App alg $ Cons y r) (App alg Nil) xs
      Tree  t -> foldTree (\l y r -> App alg $ Ctr "Node" $ Tuple [l, y, r]) (App alg . Ctr "Leaf") t
      Nat   n -> foldNat n (App alg . Ctr "Succ") (App alg $ Nat 0)
      TangoLL t -> t & LL.foldTango \case
        NNF -> App alg $ Ctr "NN" Unit
        CNF x xs -> App alg $ Ctr "CN" $ Tuple [x, List xs]
        NCF y ys -> App alg $ Ctr "NC" $ Tuple [y, List ys]
        CCF x y xys -> App alg $ Ctr "CC" $ Tuple [x, y, xys]
      TangoLN t -> t & LN.foldTango \case
        NZF -> App alg $ Ctr "NZ" Unit
        CZF x xs -> App alg $ Ctr "CZ" $ Tuple [x, List xs]
        NSF n -> App alg $ Ctr "NS" $ Nat n
        CSF x xns -> App alg $ Ctr "CS" $ Tuple [x, xns]
      e -> error $ "cata is not defined for expressions of the form " ++ show (() <$ e)
    appPara :: Program h -> Program h -> Program h
    appPara alg = \case
      List xs -> paraList (\y (ys, r) -> App alg $ Cons y $ Tuple [r, List ys]) (App alg Nil) xs
      Tree xs -> paraTree (\l t y r u -> App alg $ Ctr "Node" $ Tuple [Tuple [l, Tree t], y, Tuple [r, Tree u]]) (App alg . Ctr "Leaf") xs
      Nat   n -> paraNat (\(i, r) -> App alg $ Ctr "Succ" $ Tuple [r, Nat i]) (App alg (Nat 0)) n
      e -> error $ "para is not defined for expressions of the form " ++ show (() <$ e)

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
  where Tree t = foldTree (\l x r -> Ctr "Node" $ Tuple [l, x, r]) (Ctr "Leaf") t

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

foldNat :: Nat -> (a -> a) -> a -> a
foldNat 0 _ e = e
foldNat n f e = f (foldNat (n - 1) f e)

pattern Nat :: Nat -> Expr l h
pattern Nat n <- (unNat -> Just n)
  where Nat n = foldNat n Succ Zero

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

-- * Tango

mkTangoLL :: TangoListList (Expr l h) (Expr l h) -> Expr l h
mkTangoLL = \case
  NN -> Ctr "NN" $ Tuple []
  CN x xs -> Ctr "CN" $ Tuple [x, List xs]
  NC y ys -> Ctr "NC" $ Tuple [y, List ys]
  CC x y xys -> Ctr "CC" $ Tuple [x, y, mkTangoLL xys]

mkTangoLN :: TangoListNat (Expr l h) -> Expr l h
mkTangoLN = \case
  NZ -> Ctr "NZ" $ Tuple []
  CZ x xs -> Ctr "CZ" $ Tuple [x, List xs]
  NS n -> Ctr "NS" $ Nat n
  CS x xns -> Ctr "CS" $ Tuple [x, mkTangoLN xns]

unTangoLL :: Expr l h -> Maybe (TangoListList (Expr l h) (Expr l h))
unTangoLL = \case
  Ctr "NN" Unit -> Just NN
  Ctr "CN" (Tuple [x, List xs]) -> Just $ CN x xs
  Ctr "NC" (Tuple [y, List ys]) -> Just $ NC y ys
  Ctr "CC" (Tuple [x, y, unTangoLL -> Just xys]) -> Just $ CC x y xys
  _ -> Nothing

pattern TangoLL :: TangoListList (Expr l h) (Expr l h) -> Expr l h
pattern TangoLL xys <- (unTangoLL -> Just xys)
  where TangoLL xys = mkTangoLL xys

unTangoLN :: Expr l h -> Maybe (TangoListNat (Expr l h))
unTangoLN = \case
  Ctr "NZ" Unit -> Just NZ
  Ctr "CZ" (Tuple [x, List xs]) -> Just $ CZ x xs
  Ctr "NS" (Nat n) -> Just $ NS n
  Ctr "CS" (Tuple [x, unTangoLN -> Just xns]) -> Just $ CS x xns
  _ -> Nothing

pattern TangoLN :: TangoListNat (Expr l h) -> Expr l h
pattern TangoLN xys <- (unTangoLN -> Just xys)
  where TangoLN xys = mkTangoLN xys
