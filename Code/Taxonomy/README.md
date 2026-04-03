# Taxonomy

This directory is the core of the project. It defines a family of monads for
computation and specification, all sharing the shape `stateT S (optionT <base>)`
and varying only in the base monad.

## Monads

| Base monad | Composed type | File | Role |
|---|---|---|---|
| `itree void1` | `prog` | `Prog.v` | Deterministic computation |
| `PureWP` = `(A -> Prop) -> Prop` | `ProgWP` | `WP.v` | Weakest precondition spec |
| `SetM` = `A -> Prop` | `ndprog` | `NonDetProg.v` | Nondeterministic computation |
| `optionT SetM` (double `optionT`) | `nditprog` | `NonDetItProg.v` | Nondeterminism + divergence |

The first row is a *computation* monad (programs that can be executed); the
remaining rows are *specification* monads (predicate transformers for reasoning).

`nditprog` uses a double `optionT` stack: the inner layer distinguishes
divergence (`None`) from convergence (`Some`), while the outer layer handles
exceptions.

## Strongest postcondition arrows (`SPost.v`)

`SPost.v` defines predicate transformer *arrows* using binary relations
`A -> B -> Prop` (`SPArr`).

Two variants share a common `SPRecord` (bundles a predicate transformer with
its underlying relation) and differ only in the correctness condition:

| Arrow | Condition | Quantifier |
|---|---|---|
| `PureASPostArr A B` | `sp_pt d pre b <-> asp (sp_rel d) pre b` | `asp R pre b = exists a, pre a /\ R a b` (angelic) |
| `PureDSLPostArr A B` | `sp_pt d pre b <-> dslp (sp_rel d) pre b` | `dslp R pre b = forall a, R a b -> pre a` (demonic) |

Composed types for stateful specifications with exceptions:

    ASPostArr S A = stateArrT S (optionArrT PureASPostArr) unit A
    DSLPostArr S A = stateArrT S (optionArrT PureDSLPostArr) unit A

`SPostFacts.v` proves `ArrowLaws` for both `PureASPostArr` and
`PureDSLPostArr`.

## Law proofs (`*Facts.v`)

Each monad has a companion `*Facts.v` file proving `MonadLawsE` (monad laws up
to `Eq1` equivalence). `ProgFacts.v` provides generic `optionT` and `stateT`
law instances that the other Facts files reuse — most higher-level proofs are
just instance chaining.

| File | Proves laws for |
|---|---|
| `ProgFacts.v` | `optionT M` (generic), `stateT S M` (generic), `prog` |
| `WPFacts.v` | `PureWP`, `ProgWP` |
| `SPostFacts.v` | `ArrowLaws` for `PureASPostArr`, `PureDSLPostArr` |
| `NonDetProgFacts.v` | `SetM`, `ndprog` |
| `NonDetItProgFacts.v` | `nditprog` |

## Observation functions

Observation functions bridge computation monads to specification types,
extracting program semantics as weakest preconditions (WP) or strongest
postconditions (SP).

**`Observation.v`** — maps `prog` to specs:
- `obsArrowSP`: SP via relational observation wrapped with `mkASP`
- `observationWP`: strongest WP of a deterministic program
- `observationWLP`: WP with divergence tolerance (uses `any_infinite` from ITree)

**`NonDetObservation.v`** — maps `ndprog` to specs:
- `obsArrowASP`: angelic SP via set membership
- `obsDWP` / `obsAWP`: demonic (all outcomes) / angelic (some outcome) WP

**`NonDetItObservation.v`** — maps `nditprog` to specs:
- `obsArrowASP`: collapses the three-valued outcome space into two — `Some
  (a, s')` for convergence, `None` for exceptions or divergence
- `obsDWP` / `obsDWLP`: demonic total / partial WP
- `obsAWP` / `obsAWLP`: angelic total / partial WP

The total variants (`obsDWP`, `obsAWP`) reject divergence; the partial variants
(`obsDWLP`, `obsAWLP`) accept it.

## SP variants (`SPVariants.v`)

Implements the taxonomy from Verscht & Kaminski ("A Taxonomy of Hoare-Like
Logics", POPL 2025). Four strongest postcondition transformers for each
computation monad (`prog`, `ndprog`, `nditprog`), all built from the same
reachability relation but differing in quantifier structure:

| Variant | Definition | Meaning |
|---|---|---|
| `asp` | `asp` (existential) | Angelic, total — reachable from precondition |
| `dslp` | `dslp` (universal) | Demonic, liberal — exclusively reachable, or unreachable |
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
Prog ──► ProgFacts
                   ╲
WP ──► WPFacts      ► SPost ──► SPostFacts
                   ╱        │
NonDetProg ──► NonDetProgFacts
                             ├──► Observation (uses Prog, WP, SPost)
NonDetItProg ──► NonDetItProgFacts
                             ├──► NonDetObservation (uses NonDetProg, WP, SPost)
                             ├──► NonDetItObservation (uses NonDetItProg, WP, SPost)
                             │
                             └──► SPVariants (uses Prog, NonDetProg, NonDetItProg, SPost)
```
