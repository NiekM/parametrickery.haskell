module Refinements where

import Data.List qualified as List

import Base
import Data.Named
import Language.Type
import Language.Expr
import Language.Declaration

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

-- Lifts the nth argument out of a problem.
liftArg :: Nat -> Problem -> Maybe (Text, Mono, [Term], Problem)
liftArg n (Declaration sig@Signature { context } exs)
  | n >= fromIntegral (length context) = Nothing
  | otherwise = Just
    (name, mono, exprs, Declaration sig { context = context' } exs')
  where
    (Named name mono, context') = pick n context
    (exprs, exs') = unzip $ pickEx <$> exs

    pickEx (Example (pick n -> (i, ins)) out) = (i, Example ins out)

    pick :: Nat -> [a] -> (a, [a])
    pick i xs = case splitAt (fromIntegral i) xs of
      (ys, z:zs) -> (z, ys ++ zs)
      _ -> error "Error"

-- All possible ways to lift one argument from a problem.
pickApart :: Problem -> [(Text, Mono, [Term], Problem)]
pickApart p@(Declaration Signature { context } _) =
  zipWith const [0..] context & mapMaybe (`liftArg` p)

type Refinement = Problem -> [[Problem]]

-- NOTE: this is mostly a test refinement. I don't know how precise we have to
-- get with the refinements. It could be interesting to keep refining until a
-- program is solved, but more realistic is to perform a refinement, then first
-- use a realizability technique as well as some usefulness measure to decide
-- whether to continue refining or call an external synthesizer.
introPair :: Refinement
introPair (Declaration sig@Signature { goal } exs) = case goal of
  Tup t u -> return
    [ Declaration sig { goal = t } $ exs <&> \case
      Example ins (Pair a _) -> Example ins a
      _ -> error "Type mismatch"
    , Declaration sig { goal = u } $ exs <&> \case
      Example ins (Pair _ b) -> Example ins b
      _ -> error "Type mismatch"
    ]
  _ -> []

-- Randomly removes one variable from the context. How do we show the lattice
-- structure here?
-- TODO: how do we avoid multiple shrinkings leading to the same problem? We
-- could try to rely on some dynamic programming/caching technique, but perhaps
-- better would be to annotate variables in the context as being mandatory?
-- Still, it might be necessary to perform all possible shrinkings at once?
shrinkContext :: Refinement
shrinkContext p = pickApart p <&> \(_, _, _, q) -> [q]

elimList :: Refinement
elimList p = pickApart p & mapMaybe
  \(v, t, es, Declaration s@(Signature { context }) xs) -> case t of
    List u ->
      let
        (nil, cons) = zip es xs & mapEither \case
          (Lst [], ex) -> Left ex
          (Lst (y:ys), Example ins out) ->
            Right $ Example (y : Lst ys : ins) out
          _ -> error "Expected a list!"
      in Just
        [ Declaration s nil
        -- TODO: generate fresh variables
        , Declaration s
          { context =
            Named (v <> "_h") u : Named (v <> "_t") (List u) : context
          } cons
        ]
    _ -> Nothing

-- TODO: maybe first make it work not as a refinement, but using a more
-- restricted way to introduce foldr, similar to what we did in the paper. So without using `pickApart`


-- TODO: make this work for shape complete example sets!
-- Currently it only works for exactly trace complete sets...
-- The only solution seems to be to have refinements work on container problems
-- In other words, we should translate to container functors first
-- TODO: how do we recover which argument the fold was applied to?
introFoldr :: Refinement
introFoldr p = pickApart p & mapMaybe
  -- We lift `v : t` out of the problem. `es` are the different values `v` had
  -- in the different examples.
  \(v, t, es, Declaration s@(Signature { context, goal }) xs) -> case t of
    List u ->
      let
        paired = zip es xs
        -- We compute the constraints for the nil and the cons case.
        (nil, cons) = paired & mapEither \case
          (Lst [], ex) -> Left ex
          (Lst (y:ys), Example ins out) ->

            -- Here, instead of searching in paired, we want to compute the
            -- polymorphic examples represented by `paired` and then try to
            -- apply those PolyExamples to (ys : xs). If that succeeds, it is
            -- shape complete.

            case List.lookup (Lst ys) paired of
            -- TODO: perhaps we can compute the morphisms of the examples and
            -- use those to figure out the right monomorphic recursive call.
            -- This is quite clever, we can use the polymorphic type to
            -- transform our monomorphic examples as we please to equivalent
            -- monomorphic examples.
            -- Perhaps we just check if the shape and relation occur and then
            -- fill in the positions as required.
            -- IDEA!: we should write a function that tries to apply a partial
            -- container morphism to an expression, returning the transformed
            -- expression if the input and relation matches.
            Just (Example i o) | i == ins -> do
              Right $ Example (y : o : ins) out

            -- How do we deal with trace/shape incompleteness? We can't just
            -- call an error...

            _ -> error "Trace incomplete!"
          _ -> error "Expected a list!"
      in Just
        [ Declaration s nil
        -- TODO: generate fresh variables
        , Declaration s
          { context = Named (v <> "_h") u : Named (v <> "_r") goal : context }
          cons
        ]
    _ -> Nothing

-- -- TODO: make this work for shape complete example sets!
-- -- Currently it only works for exactly trace complete sets...
-- -- The only solution seems to be to have refinements work on container problems
-- -- In other words, we should translate to container functors first
-- introFoldrPoly :: Refinement
-- introFoldrPoly p = case check p of
--   Left conflict -> error . show $ pretty conflict
--   Right examples -> pickApart p & mapMaybe
--     \(v, t, es, Problem s@(Signature { ctxt, goal }) xs) -> case t of
--       List u ->
--         let
--           paired = zip es xs
--           (nil, cons) = paired & mapEither \case
--             (Lst [], ex) -> Left ex
--             (Lst (y:ys), Example ins out) ->
--               -- TODO: how to do this???????
--               case applyMorph s examples (Lst ys : ins) of
--                 Just e -> Right $ Example (y : e : ins) out
--                 Nothing -> error "Shape incomplete!"
--             _ -> error "Expected a list!"
--         in Just
--           [ Problem s nil
--           -- TODO: generate fresh variables
--           , Problem s { ctxt = (v <> "_h", u) : (v <> "_r", goal) : ctxt } cons
--           ]
--       _ -> Nothing

-- NOTE: this is not that easy, recomputing positions becomes quite tricky
-- during refinements. We might require to have positions be not just indices,
-- but some kind of projections.
-- morphIntroFoldr :: MorphProblem -> [[MorphProblem]]
-- morphIntroFoldr p = _
