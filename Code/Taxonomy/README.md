# Taxonomy

This directory is the core of the project. It defines a family of monads for
computation and specification, all sharing the shape `stateT S (optionT <base>)`
and varying only in the base monad.

## Monads

| Base monad | Composed type | File | Role |
|---|---|---|---|
| `itree void1` | `prog` | `Prog.v` | Deterministic computation |
| `PureWP` = `(A -> Prop) -> Prop` | `ProgWP` | `WP.v` | Weakest precondition spec |
| `PureSPost` = `forall pre, {p : A -> Prop \| ...}` | `ProgSPost` | `SPost.v` | Strongest postcondition spec |
| `SetM` = `A -> Prop` | `ndprog` | `NonDetProg.v` | Nondeterministic computation |
| `optionT SetM` (double `optionT`) | `nditprog` | `NonDetItProg.v` | Nondeterminism + divergence |

The first two rows are *computation* monads (programs that can be executed); the
remaining three are *specification* monads (predicate transformers for reasoning).

`nditprog` uses a double `optionT` stack: the inner layer distinguishes
divergence (`None`) from convergence (`Some`), while the outer layer handles
exceptions.

## Monad laws (`*Facts.v`)

Each monad has a companion `*Facts.v` file proving `MonadLawsE` (monad laws up
to `Eq1` equivalence). `ProgFacts.v` provides generic `optionT` and `stateT`
law instances that the other Facts files reuse — most higher-level proofs are
just instance chaining.

| File | Proves laws for |
|---|---|
| `ProgFacts.v` | `optionT M` (generic), `stateT S M` (generic), `prog` |
| `WPFacts.v` | `PureWP`, `ProgWP` |
| `SPostFacts.v` | `PureSPost`, `ProgSPost` |
| `NonDetProgFacts.v` | `SetM`, `ndprog` |
| `NonDetItProgFacts.v` | `nditprog` |

## Observation functions

Observation functions bridge computation monads to specification monads,
extracting program semantics as weakest preconditions (WP) or strongest
postconditions (SP).

**`Observation.v`** — maps `prog` to specs:
- `observationWP`: strongest WP of a deterministic program
- `observationWLP`: WP with divergence tolerance (uses `any_infinite` from ITree)
- `observationSP`: forward extraction into `ProgSPost`

**`NonDetObservation.v`** — maps `ndprog` to specs:
- `obsDWP` / `obsAWP`: demonic (all outcomes) / angelic (some outcome) WP
- `obsASP`: angelic strongest postcondition
- `obsDSLP`: demonic strongest liberal postcondition (incomplete)

**`NonDetItObservation.v`** — maps `nditprog` to specs, with both
total/partial variants:
- `obsDWP` / `obsDWLP`: demonic total / partial WP
- `obsAWP` / `obsAWLP`: angelic total / partial WP
- `obsASP`: angelic SP
- `obsDSLP`: demonic SLP

The total variants (`obsDWP`, `obsAWP`) reject divergence; the partial variants
(`obsDWLP`, `obsAWLP`) accept it.

## Dependency graph

```
Prog ──► ProgFacts ──┬──► WP ──► WPFacts
                     │         ╲
                     │          ► Observation
                     │         ╱
                     ├──► SPost ──► SPostFacts
                     │
                     ├──► NonDetProg ──► NonDetProgFacts
                     │              ╲
                     │               ► NonDetObservation (uses WP, SPost)
                     │
                     └──► NonDetItProg ──► NonDetItProgFacts
                                      ╲
                                       ► NonDetItObservation (uses WP, SPost)
```
