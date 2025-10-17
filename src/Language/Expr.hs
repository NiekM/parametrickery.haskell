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

  , eval
  , fromVal
  ) where

import Prelude hiding (Enum(..), error)

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Foldable

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
      e -> error $ "cata is not defined for expressions of the form " ++ show (() <$ e)
    appPara :: Program h -> Program h -> Program h
    appPara alg = \case
      List xs -> paraList (\y (ys, r) -> App alg $ Cons y $ Tuple [r, List ys]) (App alg Nil) xs
      Tree xs -> paraTree (\l t y r u -> App alg $ Ctr "Node" $ Tuple [Tuple [l, Tree t], y, Tuple [r, Tree u]]) (App alg . Ctr "Leaf") xs
      Nat   n -> paraNat (\(i, r) -> App alg $ Ctr "Succ" $ Tuple [r, Nat i]) (App alg (Nat 0)) n
      e -> error $ "para is not defined for expressions of the form " ++ show (() <$ e)

type Env h = Map Name (Val h)
data Val h
  = VLit Lit
  | VTuple [Val h]
  | VCtr Name (Val h)
  | VClosure (Env h) Name (Program h)
  | VElim [(Name, Val h)]
  | VBuiltin Name [Val h]
  deriving (Eq, Ord, Show)

valTree :: Val h -> Maybe (Tree (Val h) (Val h))
valTree = \case
  VCtr "Leaf" x -> Just $ Leaf x
  VCtr "Node" (VTuple [l, x, r]) -> Node <$> valTree l <*> pure x <*> valTree r
  _ -> Nothing

pattern VTree :: Tree (Val h) (Val h) -> Val h
pattern VTree t <- (valTree -> Just t)
  where VTree t = foldTree (\l x r -> VCtr "Node" $ VTuple [l, x, r]) (VCtr "Leaf") t

pattern VNil :: Val h
pattern VNil = VCtr "[]" (VTuple [])

pattern VCons :: Val h -> Val h -> Val h
pattern VCons x xs = VCtr ":" (VTuple [x, xs])

valList :: Val h -> Maybe [Val h]
valList = \case
  VNil -> Just []
  VCons x xs -> (x:) <$> valList xs
  _ -> Nothing

mkValList :: [Val h] -> Val h
mkValList = foldr VCons VNil

pattern VZero :: Val h
pattern VZero = VCtr "Zero" (VTuple [])

pattern VSucc :: Val h -> Val h
pattern VSucc n = VCtr "Succ" n

valNat :: Val h -> Maybe Nat
valNat = \case
  VZero -> Just 0
  VSucc n -> (1+) <$> valNat n
  _ -> Nothing

pattern VTrue, VFalse :: Val h
pattern VTrue = VCtr "True" (VTuple [])
pattern VFalse = VCtr "False" (VTuple [])

fromBool :: Bool -> Val h
fromBool False = VFalse
fromBool True = VTrue

toBool :: Val h -> Either String Bool
toBool VFalse = Right False
toBool VTrue = Right True
toBool _ = Left "Not a boolean"

fromOrdering :: Ordering -> Val h
fromOrdering LT = VCtr "LT" (VTuple [])
fromOrdering EQ = VCtr "EQ" (VTuple [])
fromOrdering GT = VCtr "GT" (VTuple [])

evalApp :: Env h -> Val h -> Val h -> Either String (Val h)
evalApp env f e = case f of
  VClosure cloEnv x body ->
    eval (Map.insert x e cloEnv) body
  VElim branches -> case e of
    VCtr cname v -> do
      case lookup cname branches of
        Just arm -> evalApp env arm v
        Nothing -> Left $ "No branch for constructor: " ++ show cname
    _ -> Left "Elimination on non-constructor"
  VBuiltin "eq" [] -> Right $ VBuiltin "eq" [e]
  VBuiltin "eq" [x]
    | Just a <- fromVal x >>= toValue, Just b <- fromVal e >>= toValue
    -> Right $ fromBool (a == b)
  VBuiltin "cmp" [] -> Right $ VBuiltin "cmp" [e]
  VBuiltin "cmp" [x]
    | Just a <- fromVal x >>= toValue, Just b <- fromVal e >>= toValue
    -> Right $ fromOrdering (compareVal a b)
  VBuiltin "map" [] -> Right $ VBuiltin "map" [e]
  VBuiltin "map" [predicate]
    | Just xs <- valList e -> mkValList <$> mapM (evalApp env predicate) xs
    | otherwise -> Left "Map only works on lists"
  VBuiltin "filter" [] -> Right $ VBuiltin "filter" [e]
  VBuiltin "filter" [predicate]
    | Just xs <- valList e -> mkValList <$> filterM (evalApp env predicate >=> toBool) xs
    | otherwise -> Left "Filter only works on lists"
  VBuiltin "cata" [] -> Right $ VBuiltin "cata" [e]
  VBuiltin "cata" [alg]
    | Just xs <- valList e ->
      foldr (\x r -> r >>= evalApp env alg . VCons x) (evalApp env alg VNil) xs
    | Just n <- valNat e ->
      foldNat n (>>= evalApp env alg . VSucc) (evalApp env alg VZero)
    | Just t <- valTree e ->
      foldTree (\l x r -> do a <- l; b <- r; evalApp env alg (VCtr "Node" (VTuple [a, x, b]))) (evalApp env alg . VCtr "Leaf") t
    | otherwise -> Left $ "Cata only works on some types"
  VBuiltin "para" [] -> Right $ VBuiltin "para" [e]
  VBuiltin "para" [alg]
    | Just xs <- valList e ->
      paraList (\x (ys, r) -> do a <- r; evalApp env alg (VCons x (VTuple [a, mkValList ys]))) (evalApp env alg VNil) xs
    | Just t <- valTree e ->
      paraTree (\l u x r s -> do a <- l; b <- r; evalApp env alg (VCtr "Node" (VTuple [VTuple [a, VTree u], x, VTuple [b, VTree s]]))) (evalApp env alg . VCtr "Leaf") t
    | otherwise -> Left $ "Para only works on some types"
  _ -> Left $ "Trying to apply a non-function"

eval :: Env h -> Program h -> Either String (Val h)
eval env expr = case expr of
  Var x ->
    case Map.lookup x env of
      Just v -> Right v
      Nothing
        | x `elem` ["para", "cata", "map", "filter", "cmp", "eq"] -> Right $ VBuiltin x []
        | otherwise -> Left $ "Unbound variable: " ++ show x.getName

  Lam x body ->
    Right $ VClosure env x body

  Elim branches ->
    VElim <$> mapM (mapM $ eval env) branches

  App f e -> do
    vf <- eval env f
    ve <- eval env e
    evalApp env vf ve

  Tuple es -> VTuple <$> mapM (eval env) es

  Prj i e -> do
    v <- eval env e
    case v of
      VTuple vs ->
        if i < List.genericLength vs then Right (List.genericIndex vs i)
        else Left "Tuple index out of bounds"
      _ -> Left "Projection on non-tuple"

  Lit l -> Right $ VLit l

  Ctr name arg -> do
    arg' <- eval env arg
    Right $ VCtr name arg'

  Hole _ -> Left "Cannot evaluate holes"

fromVal :: Val h -> Maybe (Program h)
fromVal = \case
  VLit i -> Just $ Lit i
  VTuple vs -> Tuple <$> mapM fromVal vs
  VCtr c v -> Ctr c <$> fromVal v
  VClosure{} -> trace "closure" Nothing
  VElim{} -> trace "elim" Nothing
  VBuiltin{} -> trace "builtin" Nothing

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
