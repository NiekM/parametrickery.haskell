-- Exploring a deep embedding of the language. The shallow embedding (at
-- different depths) runs into the issue that we cannot easily inspect the
-- types, at least not without introducing various singleton types etc. A deep
-- embedding allows for example easy inspecting of types, including constraints,
-- as well as multiple type variables.

module Deep where

import Control.Monad (forM)
import Control.Monad.State
import Data.Bifunctor (bimap)
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

-- Type constraints.
data Ctr = None | Eq | Ord | Num
  deriving stock (Eq, Ord, Show)

data LitTyp = TInt | TNat | TBool | TStr
  deriving stock (Eq, Ord, Show)

data LitVal = VInt Int | VNat Nat | VBool Bool | VStr String
  deriving stock (Eq, Ord, Show)

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
  deriving stock (Eq, Ord, Show)
 
-- Function signatures. Each variable has a type constraint.
-- NOTE: we could consider changing this so that `vars` is just a [Var], and
-- handle the constraints separately. This would make it a bit nicer to show
-- that a type has no constraints, or multiple. However, it would make the
-- lattice structure of constraints less visible.
data Sig = Sig
  { vars :: [(Var, Ctr)]
  , ctxt :: [(Var, Typ)]
  , goal :: Typ
  } deriving stock (Eq, Ord, Show)

-- We don't really need an expression type, just a value type for the
-- input-output examples.
data Val where
  VTop :: Val
  VAnd :: Val -> Val -> Val
  VInl :: Val -> Val
  VInr :: Val -> Val
  VLst :: [Val] -> Val
  VLit :: LitVal -> Val
  deriving stock (Eq, Ord, Show)

-- The extension of a container functor.
data Ext = Ext
  { shape     :: Val
  , positions :: Map Var (Map Nat Val)
  } deriving stock (Eq, Ord, Show)

-- NOTE: if a type variable does not occur in the type, it is not listed in the
-- resulting container extension.
-- TODO: perhaps we should avoid this!
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
-- equivalence classes? Wouldn't they have the same effect? I guess the
-- difference would be a set of sets vs a list of sets.
-- NOTE: a nice thing about equivalence classes is not just the vizualization,
-- but also that it is much easier to take a subset of the relation.
data Rel
  = RNone
  | REq  (Map (Nat, Nat) Bool)
  | ROrd (Map (Nat, Nat) Ordering)
  -- TODO: note that this is not a correct way of representing a Num constraint,
  -- since it does not provide a way to produce values.
  | RNum (Map Nat Int)
  deriving stock (Eq, Ord, Show)

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Ex = Ex
  { ins :: [Val]
  , out :: Val
  } deriving stock (Eq, Ord, Show)

computeRel :: Ctr -> Map Nat Val -> Rel
computeRel c ps = case c of
  None -> RNone
  Eq   -> REq . Map.uncurry $ ps <&> \x -> ps <&> \y -> x == y
  Ord  -> ROrd . Map.uncurry $ ps <&> \x -> ps <&> \y -> compare x y
  Num  -> RNum $ ps <&> \case
    VLit (VInt n) -> n
    VLit (VNat n) -> fromIntegral n
    v -> error $ "Cannot coerce " ++ printVal 0 v ++ " to an integer."

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
extendEx :: Sig -> Ex -> (Map Var Rel, Ext, Ext)
extendEx (Sig vars ctxt goal) (Ex ins out) = (r, Ext t q', Ext s p')
  where
    m = Map.fromList $ vars <&> \(v, _) -> (v, 0)
    Ext s p = evalState (extend goal out) m
    -- NOTE: this should ensure every type variable has a (possible empty)
    -- position map
    p' = Map.unionWith Map.union p $ Map.fromList $
      vars <&> \(v, _) -> (v, Map.empty)
    -- TODO: is it really the best to turn them into a tuple?
    i = foldr TAnd TTop $ map snd ctxt
    x = foldr VAnd VTop ins
    (Ext t q) = evalState (extend i x) m
    -- NOTE: this should ensure every type variable has a (possible empty)
    -- position map. `extend` should probably already do this!
    q' = Map.unionWith Map.union q $ Map.fromList $
      vars <&> \(v, _) -> (v, Map.empty)
    r = Map.intersectionWith computeRel (Map.fromList vars) q'

data Problem = Problem
  { sig :: Sig
  , exs :: [Ex]
  } deriving stock (Eq, Ord, Show)

type Origins = Multi Nat Nat

origins :: Map Nat Val -> Map Nat Val -> Origins
origins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

type Morph = Map (Map Var Rel, Val) (Val, Map Var Origins)

-- TODO: maybe this should not use intersectionWith, but rather a unionWith with
-- a default. Although we should have some consistency: currently not having a
-- type variable in the positions is equivalent to having it map to mempty, so
-- we should only use one option and mapping to mempty seems more sensible.
toMorph :: (Map Var Rel, Ext, Ext) -> Morph
toMorph (r, Ext s p, Ext t q) =
  Map.singleton (r, s) (t, Map.intersectionWith origins p q)

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict
  deriving stock (Eq, Ord, Show)

merge :: [Morph] -> Either Conflict Morph
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- maybeToEither ShapeConflict    $ allSame ss
  p <- maybeToEither PositionConflict $ Map.unionsWithA consistent ps
  return (s, p)

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
-- TODO: check that this actually works as expected for multiple type variables.
check :: Problem -> Either Conflict Morph
check (Problem sig exs) = merge $ map (toMorph . extendEx sig) exs

------ Refinements ------

-- TODO: how are refinements already used in synthesizers? Splitting up the search space is already often done in synthesizers, but not often is realizability used to rule out some options.

-- NOTE: perhaps a refinement is a choice made about a program that is
-- consistent with the specification, where "consistency" can be whatever we
-- want. In our case, consistency means that there is a partial function that
-- would make the program complete.


-- TODO: what if the refinement returns two problems (i.e. introducing multiple
-- holes)
-- TODO: what if a refinement can be applied in multiple ways?
-- TODO: maybe it should return [[Problem]], a sum of products.
-- TODO: even better, have it return some "lattice" of problems, somehow showing
-- the relations between all of them.
-- TODO: additionally, refinements might return
-- - missing/lifted examples (e.g. due to trace incompleteness)
-- - some usefulness measure (e.g. trace incompleteness might discourage
--   introducing foldr). Can we always statically determine the usefulness, or
--   should we first perform a realizability check?
-- - some information about how this refinement relates to/influences other
--   refinements
-- - a concrete sketch/some way to recover the final program from a series of
--   refinements
type Refinement = Problem -> [[Problem]]

introPair :: Refinement
introPair (Problem (sig@Sig{ goal }) exs) = case goal of
  TAnd t u -> return
    [ Problem sig { goal = t } $ exs <&> \(Ex ins out) -> Ex ins (getFst out)
    , Problem sig { goal = u } $ exs <&> \(Ex ins out) -> Ex ins (getSnd out)
    ]
  _ -> []
  where
    getFst (VAnd a _) = a
    getFst _ = error "Type mismatch"
    getSnd (VAnd _ b) = b
    getSnd _ = error "Type mismatch"

-- Randomly removes one variable from the context. How do we show the lattice
-- structure here?
-- TODO: how do we avoid multiple shrinkings leading to the same problem? We
-- could try to rely on some dynamic programming/caching technique, but perhaps
-- better would be to annotate variables in the context as being mandatory?
-- Still, it might be necessary to perform all possible shrinkings at once?
shrinkContext :: Refinement
shrinkContext (Problem sig@Sig { ctxt } exs) = [0 .. length ctxt - 1] <&> \n ->
  return $ Problem sig { ctxt = delete n ctxt } $ exs <&>
    \(Ex ins out) -> Ex (delete n ins) out
  where
    delete :: Int -> [a] -> [a]
    delete n xs = take n xs ++ drop (n + 1) xs

-- introFoldr :: Problem -> [Problem]
-- introFoldr (Problem sig exs) = _


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

printSig :: Sig -> String
printSig (Sig vars ctxt goal) = concat
  [ parens $ List.intercalate ", " $ vars <&> \(x, c) -> show c ++ " " ++ x
  , " => "
  , braces $ List.intercalate ", "
    $ ctxt <&> \(x, t) -> x ++ " : " ++ printTyp 0 t
  , " -> "
  , printTyp 0 goal
  ]

printProblem :: String -> Problem -> String
printProblem fun (Problem sig exs) = unlines (header : examples)
  where
    header = unwords [fun, ":", printSig sig]
    examples = exs <&> \(Ex ins out) -> unwords
      (fun : map (printVal 3) ins ++ ["=", printVal 3 out])

parens, braces, brackets :: String -> String
parens   x = "(" ++ x ++ ")"
braces   x = "{" ++ x ++ "}"
brackets x = "[" ++ x ++ "]"

parensIf :: Int -> Int -> String -> String
parensIf n p s
  | n < p     = parens s
  | otherwise = s

------

class    ToVal a      where toVal :: a -> Val
instance ToVal Int    where toVal = VLit . VInt
instance ToVal Bool   where toVal = VLit . VBool
instance ToVal Nat    where toVal = VLit . VNat
instance ToVal String where toVal = VLit . VStr
instance ToVal ()     where toVal = const VTop

instance ToVal a => ToVal [a] where
  toVal = VLst . map toVal

instance (ToVal a, ToVal b) => ToVal (a, b) where
  toVal = uncurry VAnd . bimap toVal toVal

instance (ToVal a, ToVal b) => ToVal (Either a b) where
  toVal = either VInl VInr . bimap toVal toVal

------ Examples ------

sg :: Sig
sg = Sig [("a", Eq)] [("x", TVar "a"), ("xs", TLst (TVar "a"))]
  (TLst (TVar "a"))

-- TODO: change ex to something that makes sense.
-- TODO: in general, give some better working examples here.
ex :: Ex
ex = Ex [toVal @Nat 3, toVal @[Nat] [2, 4]] (toVal @[Nat] [2, 2])

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
    v1 = toVal @Nat 1; v2 = toVal @Nat 2

-- >>> printProblem "test" prb
-- "test : (None a) => {x : a, y : a, z : a} -> a\ntest 1 2 2 = 2\ntest 2 1 2 = 2\ntest 2 2 1 = 2\n"

-- >>> check prb
-- Left PositionConflict

pairExample :: Problem
pairExample = Problem
  { sig = Sig
    { vars = [("a", None), ("b", None)]
    , ctxt = [("x", TVar "a"), ("y", TVar "b")]
    , goal = TAnd (TVar "a") (TVar "b")
    }
  , exs =
    [ Ex [toVal @Nat 1, toVal True ] $ toVal @(Nat, Bool) (1, True )
    , Ex [toVal False, toVal @Int 3] $ toVal @(Bool, Int) (False, 3)
    ]
  }

-- >>> printProblem "pair" pairExample
-- "pair : (None a, None b) => {x : a, y : b} -> a * b\npair 1 True = (1 , True)\npair 3 False = (3 , False)\n"

introPairExample :: [[Problem]]
introPairExample = introPair pairExample

-- >>> fmap (fmap (printProblem "f")) introPairExample
-- [["f : (None a, None b) => {x : a, y : b} -> a\nf 1 True = 1\nf False 3 = False\n","f : (None a, None b) => {x : a, y : b} -> b\nf 1 True = True\nf False 3 = 3\n"]]
