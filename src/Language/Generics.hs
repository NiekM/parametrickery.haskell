{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Language.Generics
  ( toData
  , FromExpr(..)
  , ToExpr(..)
  , Interpret(..)
  ) where

import GHC.Generics hiding (Constructor)
import GHC.TypeLits (KnownSymbol, symbolVal)

import Data.Void
import Data.Kind
import Data.Proxy

import Data.Some
import Data.Tree.Binary

import Base

import Language.Expr
import Language.Type
import Language.Pretty ()

-- | Interpret a program as a Haskell function.
class Interpret a where
  interpret :: Program Void -> a

instance {-# OVERLAPPING #-} FromExpr a => Interpret a where
  interpret e = case eval mempty e of
    Left err -> error err
    Right v -> case fromVal v >>= toValue >>= fromExpr of
      Nothing -> error "Not a value"
      Just x -> x

instance {-# OVERLAPPING #-}
  (ToExpr a False, Interpret b) => Interpret (a -> b) where
  interpret p = interpret . App p . Value . toExpr

symbolName :: forall s -> KnownSymbol s => Name
symbolName s = fromString . symbolVal $ Proxy @s

-- | Turn a Haskell value of type `a` into a `Value` (embedding).
class ToExpr a l where
  toExpr :: a -> Expr l h

  default toExpr :: (Generic a, GToExpr (Rep a) l) => a -> Expr l h
  toExpr = gtoExpr . from

instance ToExpr (Expr l Void) l where
  toExpr = fmap absurd

instance ToExpr Int l where
  toExpr = Lit . MkInt

instance ToExpr Nat l where
  toExpr = Nat

instance ToExpr () l where
  toExpr () = Tuple []

instance (ToExpr a l, ToExpr b l) => ToExpr (a, b) l where
  toExpr (x, y) = Tuple [toExpr x, toExpr y]

instance (ToExpr a l, ToExpr b l, ToExpr c l) => ToExpr (a, b, c) l where
  toExpr (x, y, z) = Tuple [toExpr x, toExpr y, toExpr z]

instance ToExpr Bool l
instance ToExpr Ordering l
instance ToExpr a l => ToExpr (Maybe a) l
instance ToExpr a l => ToExpr [a] l
instance ToExpr a l => ToExpr (Some a) l
instance (ToExpr a l, ToExpr b l) => ToExpr (Either a b) l
instance (ToExpr a l, ToExpr b l) => ToExpr (Tree a b) l

class GToExpr f l where
  gtoExpr :: f a -> Expr l h
 
instance GToExpr U1 l where
  gtoExpr _ = Unit

instance ToExpr c l => GToExpr (K1 i c) l where
  gtoExpr (K1 c) = toExpr c

instance GToExpr f l => GToExpr (D1 c f) l where
  gtoExpr (M1 p) = gtoExpr p

instance GToExpr f l => GToExpr (S1 c f) l where
  gtoExpr (M1 p) = gtoExpr p

instance (KnownSymbol c, GToExpr f l) => GToExpr (C1 (MetaCons c g s) f) l where
  gtoExpr (M1 p) = Ctr (symbolName c) $ gtoExpr p

instance (GToExpr a l, GToExpr b l) => GToExpr (a :+: b) l where
  gtoExpr (L1 p) = gtoExpr p
  gtoExpr (R1 p) = gtoExpr p

instance (GToExpr a l, GToExpr b l) => GToExpr (a :*: b) l where
  gtoExpr (a :*: b) = tuple $ gtoExpr a : projections (gtoExpr b)

-- | Turn a `Value` into a Haskell value of type `a` (extraction).
class FromExpr a where
  fromExpr :: Value -> Maybe a

  default fromExpr :: (Generic a, GFromExpr (Rep a)) => Value -> Maybe a
  fromExpr = fmap to . gfromExpr

instance FromExpr Int where
  fromExpr = \case
    Lit (MkInt i) -> Just i
    _ -> Nothing

instance FromExpr Nat where
  fromExpr = \case
    Nat n -> Just n
    _ -> Nothing

instance FromExpr () where
  fromExpr = \case
    Tuple [] -> Just ()
    _ -> Nothing

instance (FromExpr a, FromExpr b) => FromExpr (a, b) where
  fromExpr = \case
    Tuple [x, y] -> liftA2 (,) (fromExpr x) (fromExpr y)
    _ -> Nothing

instance (FromExpr a, FromExpr b, FromExpr c) => FromExpr (a, b, c) where
  fromExpr = \case
    Tuple [x, y, z] -> liftA3 (,,) (fromExpr x) (fromExpr y) (fromExpr z)
    _ -> undefined

instance FromExpr Bool
instance FromExpr Ordering
instance FromExpr a => FromExpr (Maybe a)
instance FromExpr a => FromExpr [a]
instance (FromExpr a, FromExpr b) => FromExpr (Either a b)
instance (FromExpr a, FromExpr b) => FromExpr (Tree a b)

class GFromExpr f where
  gfromExpr :: Value -> Maybe (f a)

instance GFromExpr U1 where
  gfromExpr = \case
    Unit -> Just U1
    _ -> Nothing

instance FromExpr c => GFromExpr (K1 i c) where
  gfromExpr = fmap K1 . fromExpr

instance GFromExpr f => GFromExpr (D1 c f) where
  gfromExpr = fmap M1 . gfromExpr

instance GFromExpr f => GFromExpr (S1 c f) where
  gfromExpr = fmap M1 . gfromExpr

instance (KnownSymbol c, GFromExpr f) => GFromExpr (C1 (MetaCons c g s) f) where
  gfromExpr = \case
    Ctr d e | d == symbolName c -> M1 <$> gfromExpr e
    _ -> Nothing

instance (GFromExpr a, GFromExpr b) => GFromExpr (a :+: b) where
  gfromExpr e = case gfromExpr e of
    Just x -> Just $ L1 x
    Nothing -> R1 <$> gfromExpr e

instance (GFromExpr a, GFromExpr b) => GFromExpr (a :*: b) where
  gfromExpr = \case
    Tuple (x:xs) -> liftA2 (:*:) (gfromExpr x) (gfromExpr $ tuple xs)
    _ -> Nothing

-- | Types that can be represented as `Mono`.
class ToType a where
  toType :: forall b -> a ~ b => Mono

  default toType :: (Generic a, GToType (Rep a)) => forall b -> a ~ b => Mono
  toType _ = gtoType (Rep a)

data A deriving (Eq, Ord, Show, Generic)
data B deriving (Eq, Ord, Show, Generic)

instance ToType A where
  toType _ = Free "a"

instance ToType B where
  toType _ = Free "b"

instance ToType Int where
  toType _ = Base Int

dataName :: forall a -> DataName (Rep a) => Name
dataName a = dname (Rep a)

class DataName f where
  dname :: forall g -> f ~ g => Name

instance KnownSymbol n => DataName (D1 (MetaData n m p nt) f) where
  dname _ = symbolName n

instance {-# OVERLAPPABLE #-} DataName (Rep a) => ToType a where
  toType t = Data (dataName t) []

instance {-# OVERLAPPABLE #-} (DataName (Rep (f a)), ToType a) =>
  ToType (f a) where
  toType t = Data (dataName t) [toType a]

instance {-# OVERLAPPABLE #-} (DataName (Rep (f a b)), ToType a, ToType b) =>
  ToType (f a b) where
  toType t = Data (dataName t) [toType a, toType b]

class GToType f where
  gtoType :: forall g -> f ~ g => Mono

instance GToType U1 where
  gtoType _ = Top

instance ToType c => GToType (K1 i c) where
  gtoType _ = toType c

instance GToType f => GToType (S1 m f) where
  gtoType _ = gtoType f

instance (GToType f, GToType g) => GToType (f :*: g) where
  gtoType _ = Product $ gtoType f : projections (gtoType g)

-- | Compute the `DataDef` representation of a type `k`.
class ToData (f :: k) where
  toData :: forall g -> f ~ g => Named DataDef

instance GToData (Rep a) => ToData (a :: Type) where
  toData _ = gdatatype (Rep a) <&> DataDef []

instance (GToData (Rep (f A)), Generic (f A)) =>
  ToData (f :: Type -> Type) where
  toData _ = gdatatype (Rep (f A)) <&> DataDef ["a"]

instance (GToData (Rep (f A B)), Generic (f A B)) =>
  ToData (f :: Type -> Type -> Type) where
  toData _ = gdatatype (Rep (f A B)) <&> DataDef ["a", "b"]

-- TODO: it seems that this does not work if one of the constructors has the
-- same name as the type itself...
class GToData f where
  gdatatype :: forall g -> f ~ g => Named [Constructor]

instance (GConstructors f, KnownSymbol n) =>
  GToData (D1 (MetaData n m p nt) f) where
  gdatatype _ = Named (symbolName n) (gconstructors f)

class GConstructors f where
  gconstructors :: forall g -> f ~ g => [Constructor]

instance (KnownSymbol c, GToType f) =>
  GConstructors (C1 (MetaCons c g s) f) where
  gconstructors _ = [Named (symbolName c) (gtoType f)]

instance (GConstructors f, GConstructors g) => GConstructors (f :+: g) where
  gconstructors _ = gconstructors f ++ gconstructors g
