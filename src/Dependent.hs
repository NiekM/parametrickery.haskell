{-# LANGUAGE TypeFamilies, FunctionalDependencies #-}
module Dependent (module Dependent) where

import Map

import Data.SBV
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple (untuple)
import Numeric.Natural
import Data.Kind
import Data.Map (Map)
import Data.Map qualified as Map
import Data.List (genericLength)
import Data.Void

import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
-- import Data.Functor.Sum

-- class Container (f :: Type -> Type) where
--   type Shape f :: Type
--   type Position f :: Type
--   dependence :: Shape f -> Position f -> Symbolic ()

-- instance Container [] where
--   type Shape [] = Natural

-- data Container s p a = Container
--   { shape :: s
--   , position :: p -> a
--   }

-- class Dependent s p where
--   dependence :: s -> p -> Symbolic ()



-- class Dependent a b where
--   constrain :: a -> b -> Symbolic ()

-- type SNat = SBV Natural

-- test :: Symbolic ()
-- test = do
--   n :: SNat <- symbolic "n"
--   constrain $ n .>= 3

--   data Container s p = Container
--     { checkShape :: SBV s -> SBool
--     , checkPosition :: SBV s -> SBV p -> SBool
--     }

--   nat :: SInteger -> SBool
--   nat n = n .>= 0

--   fin :: SInteger -> SInteger -> SBool
--   fin n m = nat m .&& m .< n

--   listContainer :: Container Integer Integer
--   listContainer = Container nat fin

--   inOut :: SymVal q => Container s p -> Container t q
--     -> (SBV s, SBV p -> SBV c)
--     -> (SBV t, SBV q -> SBV c)
--     -> (SBV s -> SBV t)
--     -> (SBV s -> SBV q -> SBV p)
--     -> Symbolic ()
--   inOut c1 c2 (s, p) (t, q) u g = do
--     constrain $ checkShape c1 s
--     constrain $ checkShape c2 t
--     constrain $ u s .== t
--     constrain \(Forall x) -> checkPosition c2 t x .=>
--       let y = g s x in checkPosition c1 s y .&& p y .== q x

class SymVal (UnRefined a) => Refined a where
  type UnRefined a
  refine :: proxy a -> SBV (UnRefined a) -> SBool

symbolicR :: Refined a => proxy a -> String -> Symbolic (SBV (UnRefined a))
symbolicR p s = do
  x <- symbolic s
  constrain $ refine p x
  return x

class (Refined a, SymVal (InDependent a b)) => Dependent a b where
  type InDependent a b
  depend :: proxy a b -> SBV (UnRefined a) -> SBV (InDependent a b) -> SBool

-- symbolicD :: (Refined a, SymVal (UnRefined a)) => proxy a b -> String -> Symbolic (SBV (InDependent a b))
-- symbolicD p s = do
--   x <- symbolic s
--   constrain $ refine p x
--   return x

instance Refined Void where
  type UnRefined Void = Integer
  refine _ _ = sFalse

instance Refined () where
  type UnRefined () = Integer
  refine _ n = n .== 0

instance (Refined a, Refined b) => Refined (a, b) where
  type UnRefined (a, b) = (UnRefined a, UnRefined b)
  refine _ a = let (x, y) = untuple a in refine @a undefined x .&& refine @b undefined y

instance Refined Natural where
  type UnRefined Natural = Integer
  refine _ n = n .>= 0

natural :: Symbolic SInteger
natural = symbolicR @Natural undefined "n"

newtype Fin = Fin Natural
  deriving newtype (Eq, Ord, Read, Show, Enum, Num)

-- We could also just use Identity, does that make sense?
newtype K a = K a
  deriving newtype (Eq, Ord, Read, Show)

instance (Refined k, Refined a) => Dependent k (K a) where
  type InDependent k (K a) = UnRefined a
  depend _ _ x = refine @a undefined x

-- instance (Dependent a b, Dependent c d) => Dependent (a, c) (b, d) where
--   type InDependent (a, c) (b, d) = (InDependent a b, InDependent c d)
  -- refine _ a = let (x, y) = untuple a in refine @a undefined x .&& refine @b undefined y

instance (Dependent a b, Dependent c d) => Dependent (a, c) (Either b d) where
  type InDependent (a, c) (Either b d) = Either (InDependent a b) (InDependent c d)
  depend _ a = let (x, y) = untuple a in SBV.either (depend @a @b undefined x) (depend @c @d undefined y)

-- instance Dependent () Void where
--   type InDependent () Void = Integer
--   depend _ _ x = _

instance Dependent Natural Fin where
  type InDependent Natural Fin = Integer
  depend _ m n = n .>= 0 .&& n .< m

-- fin :: SInteger -> Symbolic SInteger
-- fin x = 

type Extension f a = (Shape f, Map (Position f) a)
  -- data Extension f a = Extension
  --   { shape :: Shape f
  --   , position :: Map (Position f) a
  --   }

class (Refined (Shape f), Dependent (Shape f) (Position f), Ord (Position f)) => Container (f :: Type -> Type) where
  type Shape f
  type Position f

  to :: f a -> Extension f a
  from :: Extension f a -> f a

instance Container Identity where
  type Shape Identity = ()
  type Position Identity = K ()

  to (Identity a) = ((), Map.singleton (K ()) a)
  from = Identity . (Map.! K ()) . snd

instance Refined k => Container (Const k) where
  type Shape (Const k) = k
  type Position (Const k) = K Void

  to (Const k) = (k, mempty)
  from = Const . fst

instance (Container f, Container g) => Container (Product f g) where 
  type Shape (Product f g) = (Shape f, Shape g)
  type Position (Product f g) = Either (Position f) (Position g)

  to (Pair x y) =
    let
      (s, p) = to x
      (t, q) = to y
    in ((s, t), Map.union (Map.mapKeysMonotonic Left p) (Map.mapKeysMonotonic Right q))
  from ((s, t), m) =
    let (p, q) = Map.splitEitherMap m
    in Pair (from (s, p)) (from (t, q))

instance Container [] where
  type Shape [] = Natural
  type Position [] = Fin
  
  to xs = (genericLength xs, Map.fromList (zip [0..] xs))
  from = Map.elems . snd

