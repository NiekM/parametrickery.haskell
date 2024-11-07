{-# LANGUAGE UndecidableInstances #-}

module Language.Generics
  ( toData
  , FromExpr(..)
  , ToExpr(..)
  ) where

import GHC.Generics hiding (Constructor)
import GHC.TypeLits (KnownSymbol, symbolVal)

import Data.Maybe (fromJust)
import Data.Void
import Data.Kind
import Data.Proxy

import Base

import Language.Expr
import Language.Type

symbolName :: KnownSymbol s => proxy s -> Name
symbolName = fromString . symbolVal

class ToExpr a where
  toExpr :: a -> Value

  default toExpr :: (Generic a, GToExpr (Rep a)) => a -> Value
  toExpr = gToExpr . from

instance ToExpr Int where
  toExpr = Lit . MkInt

instance ToExpr Nat where
  toExpr = Nat

instance ToExpr () where
  toExpr () = Tuple []

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
  toExpr (x, y) = Tuple [toExpr x, toExpr y]

instance (ToExpr a, ToExpr b, ToExpr c) => ToExpr (a, b, c) where
  toExpr (x, y, z) = Tuple [toExpr x, toExpr y, toExpr z]

instance ToExpr Bool
instance ToExpr Ordering
instance ToExpr a => ToExpr (Maybe a)
instance ToExpr a => ToExpr [a]
instance (ToExpr a, ToExpr b) => ToExpr (Either a b)

class GToExpr f where
  gToExpr :: f a -> Value
 
instance GToExpr U1 where
  gToExpr _ = Unit

instance ToExpr c => GToExpr (K1 i c) where
  gToExpr (K1 c) = toExpr c

instance GToExpr f => GToExpr (D1 c f) where
  gToExpr (M1 p) = gToExpr p

instance GToExpr f => GToExpr (S1 c f) where
  gToExpr (M1 p) = gToExpr p

instance (KnownSymbol c, GToExpr f) => GToExpr (C1 (MetaCons c g s) f) where
  gToExpr (M1 p) = Ctr (symbolName @c Proxy) $ gToExpr p

instance (GToExpr a, GToExpr b) => GToExpr (a :+: b) where
  gToExpr (L1 p) = gToExpr p
  gToExpr (R1 p) = gToExpr p

instance (GToExpr a, GToExpr b) => GToExpr (a :*: b) where
  gToExpr (a :*: b) = Tuple $ gToExpr a : projections (gToExpr b)

class FromExpr a where
  fromExpr :: Program Void -> a

  default fromExpr :: (Generic a, GFromExpr (Rep a)) => Program Void -> a
  fromExpr = to . fromJust . gFromExpr

instance (ToExpr a, FromExpr b) => FromExpr (a -> b) where
  fromExpr e = fromExpr . norm mempty . App e . Value . toExpr

instance FromExpr Int where
  fromExpr = \case
    Lit (MkInt i) -> i
    _ -> undefined

instance FromExpr Nat where
  fromExpr = \case
    Nat n -> n
    _ -> undefined

instance FromExpr () where
  fromExpr = \case
    Tuple [] -> ()
    _ -> undefined

instance (FromExpr a, FromExpr b) => FromExpr (a, b) where
  fromExpr = \case
    Tuple [x, y] -> (fromExpr x, fromExpr y)
    _ -> undefined

instance (FromExpr a, FromExpr b, FromExpr c) => FromExpr (a, b, c) where
  fromExpr = \case
    Tuple [x, y, z] -> (fromExpr x, fromExpr y, fromExpr z)
    _ -> undefined

instance FromExpr Bool
instance FromExpr Ordering
instance FromExpr a => FromExpr (Maybe a)
instance (FromExpr a, FromExpr b) => FromExpr (Either a b)
instance FromExpr a => FromExpr [a]

class GFromExpr f where
  gFromExpr :: Program Void -> Maybe (f a)

instance GFromExpr U1 where
  gFromExpr = \case
    Unit -> Just U1
    _ -> Nothing

instance FromExpr c => GFromExpr (K1 i c) where
  gFromExpr = fmap K1 . Just . fromExpr

instance GFromExpr f => GFromExpr (D1 c f) where
  gFromExpr = fmap M1 . gFromExpr

instance GFromExpr f => GFromExpr (S1 c f) where
  gFromExpr = fmap M1 . gFromExpr

instance (KnownSymbol c, GFromExpr f) => GFromExpr (C1 (MetaCons c g s) f) where
  gFromExpr = \case
    Ctr c e | c == symbolName @c Proxy -> M1 <$> gFromExpr e
    _ -> Nothing

instance (GFromExpr a, GFromExpr b) => GFromExpr (a :+: b) where
  gFromExpr e = case gFromExpr e of
    Just x -> Just $ L1 x
    Nothing -> R1 <$> gFromExpr e

instance (GFromExpr a, GFromExpr b) => GFromExpr (a :*: b) where
  gFromExpr = \case
    Tuple (x:xs) -> liftA2 (:*:) (gFromExpr x) (gFromExpr $ tuple xs)
    _ -> Nothing

class ToType a where
  toType :: proxy a -> Mono

  default toType :: (Generic a, GToType (Rep a)) => proxy a -> Mono
  toType _ = gToType @(Rep a) Proxy

data A deriving (Eq, Ord, Show, Generic)
data B deriving (Eq, Ord, Show, Generic)

instance ToType A where
  toType _ = Free "a"

instance ToType B where
  toType _ = Free "b"

instance ToType Int where
  toType _ = Base Int

dataName :: forall (a :: Type) proxy. DataName (Rep a) => proxy a -> Name
dataName _ = dname $ Proxy @(Rep a)

class DataName f where
  dname :: proxy f -> Name

instance KnownSymbol n => DataName (D1 (MetaData n m p nt) f) where
  dname _ = symbolName @n Proxy

instance {-# OVERLAPPABLE #-} DataName (Rep a) => ToType a where
  toType _ = Data name []
    where name = dataName @a Proxy

instance {-# OVERLAPPABLE #-} (DataName (Rep (f a)), ToType a) =>
  ToType (f a) where
  toType _ = Data name [toType @a Proxy]
    where name = dataName @(f a) Proxy

instance {-# OVERLAPPABLE #-} (DataName (Rep (f a b)), ToType a, ToType b) =>
  ToType (f a b) where
  toType _ = Data name [toType @a Proxy, toType @b Proxy]
    where name = dataName @(f a b) Proxy

class GToType f where
  gToType :: proxy f -> Mono

instance GToType U1 where
  gToType _ = Top

instance ToType c => GToType (K1 i c) where
  gToType _ = toType @c Proxy

instance GToType f => GToType (S1 m f) where
  gToType _ = gToType @f Proxy

instance (GToType f, GToType g) => GToType (f :*: g) where
  gToType _ = Product $ gToType @f Proxy : projections (gToType @g Proxy)

mkData :: forall a proxy. GToData (Rep a) => proxy a -> DataDef
mkData _ = gdatatype @(Rep a) Proxy

mkData1 :: forall f proxy. (GToData (Rep (f A)), Generic (f A)) =>
  proxy f -> DataDef
mkData1 _ = (mkData @(f A) Proxy) { arguments = ["a"] }

mkData2 :: forall f proxy. (GToData (Rep (f A B)), Generic (f A B)) =>
  proxy f -> DataDef
mkData2 _ = (mkData @(f A B) Proxy) { arguments = ["a", "b"] }

class ToData (f :: k) where
  toData :: proxy f -> DataDef

instance GToData (Rep a) => ToData (a :: Type) where
  toData _ = mkData @a Proxy

instance (GToData (Rep (f A)), Generic (f A)) =>
  ToData (f :: Type -> Type) where
  toData _ = mkData1 @f Proxy

instance (GToData (Rep (f A B)), Generic (f A B)) =>
  ToData (f :: Type -> Type -> Type) where
  toData _ = mkData2 @f Proxy

class GToData f where
  gdatatype :: proxy f -> DataDef

instance (GConstructors f, KnownSymbol n) =>
  GToData (D1 (MetaData n m p nt) f) where
  gdatatype _ =
    DataDef (symbolName @n Proxy) [] (gconstructors @f Proxy)

class GConstructors f where
  gconstructors :: proxy f -> [Constructor]

instance (KnownSymbol c, GToType f) =>
  GConstructors (C1 (MetaCons c g s) f) where
  gconstructors _ = [Named (symbolName @c Proxy) (gToType @f Proxy)]

instance (GConstructors f, GConstructors g) => GConstructors (f :+: g) where
  gconstructors _ = gconstructors @f Proxy ++ gconstructors @g Proxy
