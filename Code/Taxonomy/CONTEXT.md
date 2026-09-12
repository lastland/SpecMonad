# Taxonomy context

Parent: [Code context](../CONTEXT.md).
Detailed semantics, naming conventions, and examples: [Taxonomy README](README.md).

## Purpose and scope

This development connects effectful computation monads to specification monads
and arrows through observations. It also compares the resulting transformers
and triples. Use the README for the full taxonomy and presentation equivalences.

## Established terms and source anchors

- A **computation** supplies operations and outcomes; for example,
  [`stdivexcnd`](ComputationMonads/StDivExcNonDet.v) represents state,
  nondeterminism, exceptions, and divergence with two option layers.
- A **specification** constrains predicates independently of a concrete
  computation. [`WPure`](BaseSpecMonads/WPureMonad.v) bundles monotone WP
  transformers; [SP carriers](BaseSpecMonads/SPPredicateTransformers.v) take
  a precondition and an outcome. Their well-formed subsets supply SP monads.
- An **observation** maps a computation to a specification. Its `obs*_ret`
  and `obs*_bind` laws relate the actual source and target operations;
  see [full-outcome SP observations](EffectObservations/SP/StDivNonDet_SPStExc.v).
- **Over / Under** compare an observed postcondition with an asserted one
  in opposite directions. [Shared arrow judgments](EffectObservations/SP/SPostArrObservation.v)
  define these over specifications already observed into ASP/DSLP arrows.

## Dependency boundaries

- [Base specification monads](BaseSpecMonads/CONTEXT.md) and
  [specification arrows](Arrows/CONTEXT.md) do not depend on concrete
  computation monads. The generic [TransformerLaws](ComputationMonads/TransformerLaws.v)
  resides in `ComputationMonads/`, but is parametric in the base monad.
- [Effect observations](EffectObservations/CONTEXT.md) connect the two sides.
  `SP/` and `WP/` define observations and their local laws;
  `EffectObservations/Taxonomy_*.v` holds the cross-observation taxonomy.
- [ExampleProgramDefs.v](ExampleProgramDefs.v) supplies shared programs without
  importing observations. [InCorrectnessPrinciples.v](InCorrectnessPrinciples.v)
  consumes the current base-monad ASP triples.

## Semantic traps

- `None` is not uniformly divergence: the computation and observed outcome
  indexing determine whether it denotes an exception or divergence.
- `SPStExc` describes an option-indexed carrier; its name alone does not fix
  the observed effect. A terminating-slice observation can hide divergence.
- SP well-formedness, monad laws, precondition monotonicity, and ordered bind
  are separate properties; see the [ordered-bind counterexamples](BaseSpecMonads/SPBindOrderCounterexample.v).
- [OldSP](OldSP/CONTEXT.md) retains built results as well as two excluded
  modules. Consult [the build manifest](../_CoqProject), not directory names,
  for inclusion; `deprecated/` is excluded.

## Reading order

1. Read the [README organizing principle](README.md), then
   [computation semantics](ComputationMonads/CONTEXT.md).
2. Choose [base monads](BaseSpecMonads/CONTEXT.md) or [arrows](Arrows/CONTEXT.md)
   for the target presentation.
3. Follow [SP](EffectObservations/SP/CONTEXT.md) or
   [WP](EffectObservations/WP/CONTEXT.md) to the source/target observation.
4. Read its [comparison layer](EffectObservations/CONTEXT.md) and worked examples.
