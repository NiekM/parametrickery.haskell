module Refinements where

import Data.Text qualified as Text
import Data.List qualified as List

import Base
import Data.Named
import Language.Type
import Language.Expr
import Language.Declaration
import Language.Container

import Utils

------ Refinements ------

-- TODO: how are refinements already used in synthesizers? Splitting up the search space is already often done in synthesizers, but not often is realizability used to rule out some options.

{-

What exactly do we expect from a refinement?

- It is a choice/assumption made about a program that is consistent with the
  specification, where "consistency" in our case means that there exists a
  (partial) function that would complete the program.
- Refinements can be applied in multiple ways.
- Refinements can introduce multiple new problems.
- Refinements can have some relation to other refinements (perhaps a lattice
  structure should be inherent to the refinements?).
- Should they take into account missing examples (e.g. due to trace
  completeness?)
- some usefulness measure (e.g. trace incompleteness might discourage
  introducing foldr). Can we always statically determine the usefulness, or
  should we first perform a realizability check?
- some information about how this refinement relates to/influences other
  refinements
- a concrete sketch/some way to recover the final program from a series of
  refinements, this includes having some way to identity which branch was chosen.
- Should refinements be able to introduce new (fresh) variables?

- (!!) Refinements are like tactics! look into papers about how tactics work/are
  implemented, especially the recent paper about tactics in Haskell. Do tactics also have a lattice-like structure etc?
  See e.g. https://github.com/TOTBWF/refinery

-}

type Arg = (Mono, [Term])

-- Lifts the nth argument out of a problem.
liftArg :: Nat -> Problem -> Maybe (Named Arg, Problem)
liftArg n (Declaration sig@Signature { context } exs)
  | n >= fromIntegral (length context) = Nothing
  | otherwise = Just
    (arg <&> (, exprs), Declaration sig { context = context' } exs')
  where
    (arg, context') = pick n context
    (exprs, exs') = unzip $ pickEx <$> exs

    pickEx (Example (pick n -> (i, ins)) out) = (i, Example ins out)

    pick :: Nat -> [a] -> (a, [a])
    pick i xs = case splitAt (fromIntegral i) xs of
      (ys, z:zs) -> (z, ys ++ zs)
      _ -> error "Error"

-- All possible ways to lift one argument from a problem.
pickApart :: Problem -> [(Named Arg, Problem)]
pickApart p@(Declaration Signature { context } _) =
  zipWith const [0..] context & mapMaybe (`liftArg` p)

addArgs :: [Named Arg] -> Problem -> Problem
addArgs args Declaration { signature, bindings } =
  Declaration
    { signature = signature { context = signature.context ++ types }
    , bindings = zipWith addInputs terms bindings
    }
  where
    types = args <&> fmap fst
    terms = List.transpose $ args <&> \x -> snd x.value
    addInputs :: [Term] -> Example -> Example
    addInputs new (Example inputs output) = Example (inputs ++ new) output

-- | A disjunction of conjunctions
newtype DisCon a = DisCon [[a]]
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

instance Applicative DisCon where
  pure = DisCon . pure . pure
  liftA2 = liftM2

instance Monad DisCon where
  x >>= f = collapse $ fmap f x
    where
      collapse :: DisCon (DisCon a) -> DisCon a
      collapse xs =
        let DisCon xss = xs <&> \(DisCon ys) -> ys
        in DisCon $ xss >>= fmap concat . sequence

instance Pretty a => Pretty (DisCon a) where
  pretty (DisCon xs) = pretty xs

-- TODO: currently, composition does not take into account that a refinement can
-- only be applied in some places. Additionaly, refinements do not have some
-- notion of whether they matched or not.
type Refinement = Problem -> DisCon Problem

-- NOTE: this is mostly a test refinement. I don't know how precise we have to
-- get with the refinements. It could be interesting to keep refining until a
-- program is solved, but more realistic is to perform a refinement, then first
-- use a realizability technique as well as some usefulness measure to decide
-- whether to continue refining or call an external synthesizer.
introTuple :: Refinement
introTuple (Declaration sig@Signature { goal } exs) = case goal of
  Product ts -> DisCon . return $ zip [0..] ts <&> \(i, t) ->
      Declaration sig { goal = t } $ exs <&> \case
        Example ins (Tuple xs) -> Example ins (xs !! i)
        _ -> error "Type mismatch"
  _ -> DisCon [[]]

fromArg :: (Named Arg -> Problem -> Maybe [Problem]) -> Refinement
fromArg f p = DisCon $ uncurry f `mapMaybe` pickApart p

elimTuple :: Refinement
elimTuple = fromArg \cases
  (Named name (Product types, terms)) problem ->
    let
      values :: [[Term]]
      values = terms <&> \case
        Tuple xs -> xs
        _ -> error "Type mismatch"

      makeArg :: Nat -> Mono -> [Term] -> Named Arg
      makeArg i t xs = Named (name <> Text.pack (show i)) (t, xs)

      newArgs :: [Named Arg]
      newArgs = zipWith3 makeArg [0 ..] types (List.transpose values)
    in
      return [ addArgs newArgs problem ]
  _ _ -> Nothing

-- Randomly removes one variable from the context. How do we show the lattice
-- structure here?
-- TODO: how do we avoid multiple shrinkings leading to the same problem? We
-- could try to rely on some dynamic programming/caching technique, but perhaps
-- better would be to annotate variables in the context as being mandatory?
-- Still, it might be necessary to perform all possible shrinkings at once?
shrinkContext :: Refinement
shrinkContext p = DisCon $ pickApart p <&> \(_, q) -> [q]

elimList :: Refinement
elimList = fromArg \cases
  (Named name (List t, terms)) problem ->
    let
      (nil, cons) = zip terms problem.bindings & mapEither \case
        (Lst [], ex) -> Left ex
        (Lst (y:ys), Example ins out) ->
          Right $ Example (ins ++ [y, Lst ys]) out
        _ -> error "Expected a list!"
    in Just
      [ problem { bindings = nil }
      -- TODO: generate fresh variables
      , Declaration problem.signature
        { context = problem.signature.context ++
          [ Named (name <> "_h") t
          , Named (name <> "_t") (List t)
          ]
        } cons
      ]
  _ _ -> Nothing

-- TODO: maybe first make it work not as a refinement, but using a more
-- restricted way to introduce foldr, similar to what we did in the paper. So without using `pickApart`

introMap :: Refinement
introMap = fromArg \cases
  -- We lift `v : t` out of the problem. `es` are the different values `v` had
  -- in the different examples.
  (Named name (List given, terms))
    (Declaration signature@Signature { context, goal = List goal } examples) ->
    zip terms examples & mapM \case
      (Lst inputs, Example scope (Lst outputs)) -> do
        guard $ length inputs == length outputs
        return Declaration
          { signature = signature
            { context = context ++ [Named (name <> "_x") given]
            , goal
            }
          , bindings = zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
          }
      _ -> error "Not actually lists."
  _ _ -> Nothing

introFoldr :: Refinement
introFoldr = fromArg \cases
  (Named name (List t, terms)) problem ->
    let
      paired = zip terms problem.bindings
      -- We compute the constraints for the nil and the cons case.
      (nil, cons) = paired & mapEither \case
        (Lst [], ex) -> Left ex
        (Lst (y:ys), Example ins out) ->
          case paired & List.find \(l, x) -> l == Lst ys && x.inputs == ins of
            Just (_, x) -> return $ Example (ins ++ [y, x.output]) out
            _ -> error "Trace incomplete!"
        _ -> error "Expected a list!"
    in Just
      [ problem { bindings = nil }
      , Declaration problem.signature
        { context = problem.signature.context ++
          [ Named (name <> "_h") t
          , Named (name <> "_r") problem.signature.goal
          ]
        } cons
      ]
  _ _ -> Nothing

introFoldrPoly :: Refinement
introFoldrPoly = fromArg \cases
  (Named name (List t, terms)) problem -> do
    let paired = zip terms problem.bindings
    polyProblem <- either (const Nothing) Just $ check
      -- This is just problem with the list pulled to the front.
      -- TODO: refactor so that this is not necessary.
      Declaration
      { signature = problem.signature
        { context = Named name (List t) : problem.signature.context }
      , bindings = paired <&> \(i, Example is o) -> Example (i:is) o
      }
    let
      -- We compute the constraints for the nil and the cons case.
      (nil, cons) = paired & mapEither \case
        (Lst [], ex) -> Left ex
        (Lst (y:ys), Example ins out) ->
          let
            types = map (.value) polyProblem.signature.context
            inContainer = toContainer (Product types) (Tuple (Lst ys:ins))
          in case applyPoly inContainer polyProblem of
            Nothing -> error "Not shape complete!"
            Just c -> return $ Example (ins ++ [y, fromContainer c]) out
        _ -> error "Expected a list!"
    Just
      [ problem { bindings = nil }
      , Declaration problem.signature
        { context = problem.signature.context ++
          [ Named (name <> "_h") t
          , Named (name <> "_r") problem.signature.goal
          ]
        } cons
      ]
  _ _ -> Nothing
