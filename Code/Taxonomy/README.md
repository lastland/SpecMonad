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

## Arrow-based specification (`SPostArr*.v`)

`SPostArr.v` defines predicate transformer *arrows* — an alternative to the
monadic `PureSPost` that works with binary relations `A -> B -> Prop` instead
of unary postconditions.

Two variants share a common `SPRecord` (bundles a predicate transformer with
its underlying relation) and differ only in the correctness condition:

| Arrow | Condition | Quantifier |
|---|---|---|
| `PureASPostArr A B` | `sp_pt d pre b <-> sp (sp_rel d) pre b` | `sp R pre b = exists a, pre a /\ R a b` (angelic) |
| `PureDSPostArr A B` | `sp_pt d pre b <-> dp (sp_rel d) pre b` | `dp R pre b = forall a, R a b -> pre a` (demonic) |

Composed types for stateful specifications with exceptions:

    ASPostArr S A = stateArrT S (optionArrT PureASPostArr) unit A
    DSPostArr S A = stateArrT S (optionArrT PureDSPostArr) unit A

`SPostArrFacts.v` proves `ArrowLaws` for both `PureASPostArr` and
`PureDSPostArr`.

## Observation functions

Observation functions bridge computation monads to specification monads,
extracting program semantics as weakest preconditions (WP) or strongest
postconditions (SP).

### Monadic observations (into `ProgWP` / `ProgSPost`)

**`Observation.v`** — maps `prog` to specs:
- `observationWP`: strongest WP of a deterministic program
- `observationWLP`: WP with divergence tolerance (uses `any_infinite` from ITree)
- `observationSP`: forward extraction into `ProgSPost`

**`NonDetObservation.v`** — maps `ndprog` to specs:
- `obsDWP` / `obsAWP`: demonic (all outcomes) / angelic (some outcome) WP
- `obsASP`: angelic strongest postcondition
- `obsDSLP`: demonic strongest liberal postcondition (incomplete)

**`NonDetItObservation.v`** — maps `nditprog` to `ProgWP`:
- `obsDWP` / `obsDWLP`: demonic total / partial WP
- `obsAWP` / `obsAWLP`: angelic total / partial WP

The total variants (`obsDWP`, `obsAWP`) reject divergence; the partial variants
(`obsDWLP`, `obsAWLP`) accept it.

### Arrow-based observations (into `ASPostArr`)

**`ObservationArr.v`** — maps `prog` to `ASPostArr`:
- `obsArrowSP`: wraps reachability relation via `mkASP`

**`NonDetObservationArr.v`** — maps `ndprog` to `ASPostArr`:
- `obsArrowASP`: angelic SP via set membership

**`NonDetItObservationArr.v`** — maps `nditprog` to `ASPostArr`:
- `obsArrowASP`: collapses the three-valued outcome space into two — `Some
  (a, s')` for convergence, `None` for exceptions or divergence

## SP variants (`SPVariants.v`)

Implements the taxonomy from Verscht & Kaminski ("A Taxonomy of Hoare-Like
Logics", POPL 2025). Four strongest postcondition transformers for each
computation monad (`prog`, `ndprog`, `nditprog`), all built from the same
reachability relation but differing in quantifier structure:

| Variant | Definition | Meaning |
|---|---|---|
| `asp` | `sp` (existential) | Angelic, total — reachable from precondition |
| `dslp` | `dp` (universal) | Demonic, liberal — exclusively reachable, or unreachable |
| `dsp` | `asp /\ dslp` | Demonic, total — exclusively reachable |
| `aslp` | `asp \/ dslp` | Angelic, liberal — reachable or unreachable |

Angelic vs demonic concerns confluence (exists vs forall over initial states
reaching a final state). Liberal vs total concerns whether unreachable final
states are included.

For `nditprog`, the file proves Theorem 3.7 (square inclusions: `dsp` ⊆ `asp`
⊆ `aslp`, `dsp` ⊆ `dslp` ⊆ `aslp`) and Theorem 3.8 (contrapositive
transformers: `asp` ↔ ¬`dslp`(¬), `dsp` ↔ ¬`aslp`(¬)).

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

SPostArr ──► SPostArrFacts
         │
         ├──► ObservationArr (uses Prog)
         ├──► NonDetObservationArr (uses NonDetProg)
         ├──► NonDetItObservationArr (uses NonDetItProg)
         │
         └──► SPVariants (uses Prog, NonDetProg, NonDetItProg)
```
