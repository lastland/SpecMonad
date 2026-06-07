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
`A -> B -> Prop` (`Pred`).

Two variants share a common `SPRecord` (bundles a predicate transformer with
its underlying relation) and differ only in the correctness condition:

| Arrow | Condition | Quantifier |
|---|---|---|
| `PureASPostArr A B` | `sp_pt d pre b <-> asp (sp_rel d) pre b` | `asp R pre b = exists a, pre a /\ R a b` (angelic) |
| `PureDSLPostArr A B` | `sp_pt d pre b <-> dslp (sp_rel d) pre b` | `dslp R pre b = forall a, R a b -> pre a` (demonic) |

For the angelic case, `SPost.v` also defines a reduced representation
`PureASPostArr' A B = SPRecord' A B` that stores only the relation; its
equivalence with `PureASPostArr` is proved in `SPostFacts.v`.

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

All three observation files implement the four-variant SP taxonomy from
Verscht & Kaminski ("A Taxonomy of Hoare-Like Logics", POPL 2025), built from
a common reachability relation `obsRel` but differing in quantifier structure:

| Variant | Definition | Meaning |
|---|---|---|
| `obsASP` | `asp` (existential) | Angelic, total — reachable from precondition |
| `obsDSLP` | `dslp` (universal) | Demonic, liberal — exclusively reachable, or unreachable |
| `obsDSP` | `obsASP /\ obsDSLP` | Demonic, total — exclusively reachable |
| `obsASLP` | `obsASP \/ obsDSLP` | Angelic, liberal — reachable or unreachable |

Angelic vs demonic concerns confluence (exists vs forall over initial states
reaching a final state). Liberal vs total concerns whether unreachable final
states are included. Each file provides the square inclusions (Theorem 3.7)
and characterizations (paper Definitions 3.5 and 3.6).

**`Observation.v`** — maps `prog` to specs:
- `obsRel`: initial state reaches outcome `r` iff the computation converges
  to `ret r`
- SP: `obsASP` / `obsDSLP` / `obsDSP` / `obsASLP`
- WP: `obsAWP` / `obsDWP` (total) and `obsAWLP` / `obsDWLP` (partial, tolerate
  divergence via `any_infinite` from ITree). Because `prog` is deterministic,
  `obsWPCollapse` and `obsWLPCollapse` show angelic and demonic collapse.

**`NonDetObservation.v`** — maps `ndprog` to specs:
- `obsRel`: set membership in the outcome set
- SP: `obsASP` / `obsDSLP` / `obsDSP` / `obsASLP`
- WP: `obsDWP` (all outcomes) / `obsAWP` (some outcome). No WLP — no
  divergence.

**`NonDetItObservation.v`** — maps `nditprog` to specs:
- `obsRel`: `Some (a, s')` for convergence, `Some None` for exceptions.
  Divergence is **not** a reachable final state — it is the absence of
  reaching any final state (dual to how divergence in WP is the absence of
  termination).
- SP: `obsASP` / `obsDSLP` / `obsDSP` / `obsASLP`, plus Theorem 3.8
  contrapositive transformers (`obsASP` ↔ ¬`obsDSLP`(¬), `obsDSP` ↔
  ¬`obsASLP`(¬))
- WP: `obsDWP` / `obsDWLP` (demonic total / partial) and `obsAWP` /
  `obsAWLP` (angelic total / partial). Total variants reject divergence;
  partial variants accept it. WP inclusions correspond to Theorem 3.7.

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
                             └──► NonDetItObservation (uses NonDetItProg, WP, SPost)
```
