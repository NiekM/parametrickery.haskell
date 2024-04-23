-- Exploring a deep embedding of the language. The shallow embedding (at
-- different depths) runs into the issue that we cannot easily inspect the
-- types, at least not without introducing various singleton types etc. A deep
-- embedding allows for example easy inspecting of types, including constraints,
-- as well as multiple type variables.

module Deep where

import Control.Monad
import Control.Monad.State
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Map.Utils qualified as Map
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Utils

type Nat = Natural

------ Data Types ------

type Var = String

-- TODO: define a lattice type class.
-- Type constraints.
data Ctr = None | Eq | Ord | Num
  deriving (Eq, Ord, Show)

data LitTyp = TInt | TNat | TBool | TStr
  deriving (Eq, Ord, Show)

data LitVal = VInt Int | VNat Nat | VBool Bool | VStr String
  deriving (Eq, Ord, Show)

-- We could try to design our framework to be generic over the types and
-- expressions, by creating some type class that provides e.g. a lens to the
-- polymorphic variables. The specific datatypes used can decide how
-- deep/shallow and typed/untyped their embedding is, as long as they provide
-- the right interface.
data Typ where
  TVar :: Var -> Typ
  TTop :: Typ
  TAnd :: Typ -> Typ -> Typ
  TXor :: Typ -> Typ -> Typ
  TLst :: Typ -> Typ
  TLit :: LitTyp -> Typ
  deriving (Eq, Ord, Show)
 
-- Function signatures. Each variable has a type constraint.
data Sig = Sig
  { vars :: [(Var, Ctr)]
  , ctxt :: [(Var, Typ)]
  , goal :: Typ
  } deriving (Eq, Ord, Show)

-- We don't really need an expression type, just a value type for the
-- input-output examples.
data Val where
  VTop :: Val
  VAnd :: Val -> Val -> Val
  VInl :: Val -> Val
  VInr :: Val -> Val
  VLst :: [Val] -> Val
  VLit :: LitVal -> Val
  deriving (Eq, Ord, Show)

-- The extension of a container functor.
data Ext = Ext
  { shape     :: Val
  , positions :: Map Var (Map Nat Val)
  } deriving (Eq, Ord, Show)

extend :: Typ -> Val -> State (Map Var Nat) Ext
extend = \cases
  (TVar v) x -> do
    m <- get
    case Map.lookup v m of
      Nothing -> error "Missing variable counter!"
      Just n -> do
        put $ Map.adjust (+1) v m
        return . Ext VTop . Map.singleton v $ Map.singleton n x
  TTop VTop -> return $ Ext VTop mempty
  (TAnd t u) (VAnd x y) -> do
    Ext s p <- extend t x
    Ext r q <- extend u y
    return $ Ext (VAnd s r) $ Map.unionWith Map.union p q
  (TXor t _) (VInl x) -> do
    Ext s p <- extend t x
    return $ Ext (VInl s) p
  (TXor _ u) (VInr y) -> do
    Ext s p <- extend u y
    return $ Ext (VInr s) p
  (TLst t) (VLst xs) -> do
    r <- forM xs $ extend t
    let (ss, ps) = unzip [ (s, p) | Ext s p <- r]
    return $ Ext (VLst ss) $ Map.unionsWith Map.union ps
  (TLit _) x -> return $ Ext x mempty
  t x -> error $ "Mismatching types! " ++ show t ++ " ~~ " ++ show x

-- NOTE: perhaps creating specific relation types for Eq and Ord would be more
-- insightful. That way we also don't have to rely on Val again and would make
-- visualization of the relation easier. RelEq could e.g. be a list of
-- equivalence classes and RelEq could be an ordered list of equivalence
-- classes.
-- TODO: how would we tell the difference between ordered vs unordered lists of
-- equivalence classes? Wouldn't they have the same effect?
data Rel
  -- = Rel0
  -- | Rel1 (Map Nat Val)
  -- | Rel2 (Map (Nat, Nat) Val)
  = RNone
  | REq  (Map (Nat, Nat) Bool)
  | ROrd (Map (Nat, Nat) Ordering)
  | RNum (Map Nat Int)
  deriving (Eq, Ord, Show)

-- A container extension with a relation on its values.
-- TODO: do we really need to store the relation in Ext? perhaps it is easier to
--       return Map Var Rel as part of `extendEx`, especially since it seems
--       that we do not need to compute the relation for outputs. This relation
--       should follow from the relation on inputs, and outputs that do not
--       occur in the input already lead to a conflict.
-- data RelExt = RelExt
--   { ext :: Ext
--   , rel :: Map Var Rel
--   }

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Ex = Ex
  { ins :: [Val]
  , out :: Val
  } deriving (Eq, Ord, Show)

eq :: Val -> Val -> Val
eq x y = VLit . VBool $ x == y

cmp :: Val -> Val -> Val
cmp x y = VLit . VInt $ case compare x y of
  LT -> -1
  EQ -> 0
  GT -> 1

computeRel :: Ctr -> Map Nat Val -> Rel
computeRel c ps = case c of
  None -> RNone
  Eq   -> REq . Map.uncurry $ ps <&> \x -> ps <&> \y -> x == y
  Ord  -> ROrd . Map.uncurry $ ps <&> \x -> ps <&> \y -> compare x y
  -- TODO: do this better. Currently Num just corresponds to being able to
  -- inspect the value.
  Num  -> RNum $ ps <&> \case
    VLit (VInt n) -> n
    VLit (VNat n) -> fromIntegral n
    v -> error $ "Cannot coerce " ++ printVal 0 v ++ " to an integer."

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
extendEx :: Sig -> Ex -> (Map Var Rel, Ext, Ext)
extendEx (Sig vars ctxt goal) (Ex ins out) = (r, i, o)
  where
    m = Map.fromList $ vars <&> \(v, _) -> (v, 0)
    o = evalState (extend goal out) m
    -- TODO: is it really the best to turn them into a tuple?
    t = foldr TAnd TTop $ map snd ctxt
    x = foldr VAnd VTop ins
    i@(Ext _ ps) = evalState (extend t x) m
    r = Map.intersectionWith computeRel (Map.fromList vars) ps

data Problem = Problem
  { sig :: Sig
  , exs :: [Ex]
  } deriving (Eq, Ord, Show)

type Origins = Multi Nat Nat

origins :: Map Nat Val -> Map Nat Val -> Origins
origins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

type Morph = Map (Map Var Rel, Val) (Val, Map Var Origins)

toMorph :: (Map Var Rel, Ext, Ext) -> Morph
toMorph (r, Ext s p, Ext t q) =
  Map.singleton (r, s) (t, Map.intersectionWith origins p q)

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict
  deriving (Eq, Ord, Show)

merge :: [Morph] -> Either Conflict Morph
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- maybeToEither ShapeConflict    $ allSame ss
  p <- maybeToEither PositionConflict $ Map.unionsWithA consistent ps
  return (s, p)

check :: Problem -> Either Conflict Morph
check (Problem sig exs) = merge $ map (toMorph . extendEx sig) exs

------ Pretty Printing ------

-- TODO: can we pretty print Morph? It seems that we need the type information
-- to know which values should become variables, or alternatively Val should
-- contain some "magic" constructors for variables. Another alternative is to
-- print natural numbers to indicate the positions, but then it becomes
-- difficult to differentiate between having an Eq/Ord constraint or not.

printTyp :: Int -> Typ -> String
printTyp p = \case
  TVar var -> var
  TTop -> "1"
  TAnd x y -> parensIf 2 p (printTyp 2 x ++ " * " ++ printTyp 2 y)
  TXor x y -> parensIf 1 p (printTyp 1 x ++ " + " ++ printTyp 1 y)
  TLst lst -> brackets $ printTyp 0 lst
  TLit lit -> case lit of
    TInt  -> "Int"
    TNat  -> "Nat"
    TBool -> "Bool"
    TStr  -> "String"

printSig :: Sig -> String
printSig (Sig vars ctxt goal) = concat
  [ parens $ List.intercalate ", " $ vars <&> \(x, c) -> show c ++ " " ++ x
  , " => "
  , braces $ List.intercalate ", "
    $ ctxt <&> \(x, t) -> x ++ " : " ++ printTyp 0 t
  , " -> "
  , printTyp 0 goal
  ]

printVal :: Int -> Val -> String
printVal p = \case
  VTop     -> "-"
  VAnd x y -> parensIf 2 p (printVal 2 x ++ " , " ++ printVal 2 y)
  VInl x   -> parensIf 2 p ("inl " ++ printVal 3 x)
  VInr y   -> parensIf 2 p ("inr " ++ printVal 3 y)
  VLst lst -> brackets $ List.intercalate ", " $ map (printVal 0) lst
  VLit lit -> case lit of
    VInt  n -> show n
    VNat  n -> show n
    VBool b -> show b
    VStr  s -> show s

parens, braces, brackets :: String -> String
parens   x = "(" ++ x ++ ")"
braces   x = "{" ++ x ++ "}"
brackets x = "[" ++ x ++ "]"

parensIf :: Int -> Int -> String -> String
parensIf n p s
  | n < p     = parens s
  | otherwise = s

------ Examples ------

sg :: Sig
sg = Sig [("a", Eq)] [("x", TVar "a"), ("xs", TLst (TVar "a"))]
  (TLst (TVar "a"))

-- TODO: change ex to something that makes sense.
-- TODO: in general, give some better working examples here.
ex :: Ex
ex = Ex [VLit (VNat 3), VLst $ VLit . VNat <$> [2, 4]]
  (VLst $ VLit . VNat <$> [2, 2])


-- >>> printSig sg
-- "(Eq a) => {x : a, xs : [a]} -> [a]"

-- >>> extendEx sg ex
-- (fromList [("a",REq (fromList [((0,0),True),((0,1),False),((0,2),False),((1,0),False),((1,1),True),((1,2),False),((2,0),False),((2,1),False),((2,2),True)]))],Ext {shape = VAnd VTop (VAnd (VLst [VTop,VTop]) VTop), positions = fromList [("a",fromList [(0,VLit (VNat 3)),(1,VLit (VNat 2)),(2,VLit (VNat 4))])]},Ext {shape = VLst [VTop,VTop], positions = fromList [("a",fromList [(0,VLit (VNat 2)),(1,VLit (VNat 2))])]})

prb :: Problem
prb = Problem
  { sig = Sig
    { vars = [("a", None)]
    , ctxt = [("x", TVar "a"), ("y", TVar "a"), ("z", TVar "a")]
    , goal = TVar "a"
    }
  , exs =
    [ Ex [v1, v2, v2] v2
    , Ex [v2, v1, v2] v2
    , Ex [v2, v2, v1] v2
    ]
  } where
    v1 = VLit (VNat 1); v2 = VLit (VNat 2)

-- >>> check prb
-- Left PositionConflict
