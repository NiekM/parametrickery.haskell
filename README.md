# Example-Based Reasoning About the Realizability of Polymorphic Programs

This package accompanies the ICFP '24 paper "Example-Based Reasoning About the Realizability of Polymorphic Programs".

## Instructions

Make sure that the following are installed:

- `ghc` with version `9.8.2`
- `cabal-install` with version `3.10.3.0`
- `z3` (tested on versions `4.8.10` and `4.12.2`)

We suggest using `ghcup` to specify specific versions of `ghc` and `cabal-install`.

To run the benchmarks, use `cabal run`.

To run the testsuite, use `cabal run -- parametrickery-test`.

## Navigation

Encoding of containers into SMT-LIB is found in `Data.SBV`:

- `Data.SBV.Encode` describes how types not natively supported by SMT-LIB can be encoded by overapproximation using the nearest supertype.
- `Data.SBV.Refine` and `Data.SBV.Depend` describe how these overapproximations can be resolved for refinement types and dependent types respectively.
- `Data.SBV.Container` describes how the extensions of container functors and container morphisms can be encoded in SMT-LIB.

`Data.Container.Core` provides an interface between haskell functors and their encodings. It provides instances for most container functors. Some specialized instances can be found in `Data.Container.Specialized`.

Sketching with `map` and `foldr` is described in `Sketch.Map` and `Sketch.Foldr` respectively. These modules implement the pipelines as seen in the paper.

## Notes

In order to use a more stable version of `ghc`, we downgraded to `9.8.2` from `9.10.1`. As a result, we had to go back to using `TypeApplications` in combination with `AllowAmbiguousTypes` in `Data.SBV.Refine` and `Data.SBV.Depend`, rather than using `RequiredTypeArguments` as described in the paper.
