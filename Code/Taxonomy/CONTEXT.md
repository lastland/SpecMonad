# Taxonomy context (main)

Parent: [Code context](../CONTEXT.md).
Detailed map: [Taxonomy README](README.md).
Active sources: [Code/_CoqProject](../_CoqProject).

## Purpose and scope

Taxonomy connects effectful computations to specification monads and arrows,
then compares the observations and triples they support. This context describes
the current `main` sources. Parts of the README retain older names; use
definitions and the manifest to resolve conflicts.

## Established vocabulary and contracts

- A **computation monad** supplies operations and outcomes. For example,
  [`stdivexcnd`](ComputationMonads/StDivExcNonDet.v) distinguishes normal
  returns, exceptions, and divergence using two option layers.
- A **specification monad** supplies a carrier, return, bind, and a chosen
  equivalence. [`WPure`](BaseSpecMonads/WPureMonad.v) bundles monotone
  weakest-precondition (WP) transformers. The strongest-postcondition (SP)
  [carriers](BaseSpecMonads/SPPredicateTransformers.v) turn a precondition into
  an outcome predicate; healthiness conditions restrict these carriers to SP monads.
- An **observation** maps a computation to a specification. Its source, target,
  and treatment of outcomes determine its meaning. Where supplied, `obs*_ret`
  and `obs*_bind` relate the particular source and target operations; see
  [`FullOutcomeObs`](EffectObservations/SP/StDivNonDet_SPStExc.v).
- **Over / Under** on SP triples compare the observed and asserted
  postconditions in opposite directions. WP triples instead compare the
  computed and asserted preconditions; their constructor names vary by file.

## Ownership and dependency boundaries

- [ComputationMonads](ComputationMonads/CONTEXT.md) owns the effect models.
  Its [TransformerLaws.v](ComputationMonads/TransformerLaws.v) is generic in
  the base monad and also supports specification stacks.
- [BaseSpecMonads](BaseSpecMonads/CONTEXT.md) owns unary specifications,
  healthiness, orders, and base adjunctions without concrete computations.
- [Arrows](Arrows/CONTEXT.md) owns binary specification carriers and their
  concrete laws. These are distinct from the unary presentations; current
  imports do not form a completely separate arrow-only dependency tree.
- [EffectObservations](EffectObservations/CONTEXT.md) connects the models.
  [SP](EffectObservations/SP/CONTEXT.md) and [WP](EffectObservations/WP/CONTEXT.md)
  define observations; `EffectObservations/Taxonomy_*.v` files compare them.
- [ExampleProgramDefs.v](ExampleProgramDefs.v) shares program definitions
  without importing observations. [InCorrectnessPrinciples.v](InCorrectnessPrinciples.v)
  states rewriting rules for the current double-option `tripleASP` presentation.

## Semantic cautions

- `None` is not uniformly divergence. In a single-option computation it can
  mean exception or divergence; an observation may also discard one option layer.
- `SPStExc` names an option-indexed carrier, not a fixed interpretation of its
  extra outcome. A terminating-slice observation can retain exceptions while
  hiding divergence.
- Healthiness, monad laws, precondition monotonicity, and monotonicity of bind
  in the refinement order are separate properties. The
  [ordered-bind counterexamples](BaseSpecMonads/SPBindOrderCounterexample.v)
  concern the existing state-only DSP/ASLP binds and pointwise orders.
- [OldSP](OldSP/CONTEXT.md) mixes manifest-listed and excluded files.
  `deprecated/` is excluded; do not use it as the default source of current symbols.

## Reading order

Choose the computation and its outcome type first. Then read the target's
[base-monad](BaseSpecMonads/CONTEXT.md) or [arrow](Arrows/CONTEXT.md) contract,
the corresponding observation, and finally its comparison file and examples.
Follow the local context before relying on an older comment or a similarly
named definition from another presentation.
