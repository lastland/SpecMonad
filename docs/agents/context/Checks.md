# Checks

Parent: [Code context](Code.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Purpose and audit scope

[Assumptions.v](../../../Code/Checks/Assumptions.v) is a console audit of selected proof
dependencies. It imports existing theorems and uses `Print Assumptions`
and `Check`; its output concerns only the named declarations.

The selected reports cover:

- Core algebraic arrow helpers in [Arrow.v](../../../Code/Lib/Arrow/Arrow.v) and
  [ArrowApplyFacts.v](../../../Code/Lib/Arrow/ArrowApplyFacts.v), the fixed-input monad laws,
  and the option/state core, choice, and application law packages. The helpers
  take congruence or fixed-arrow application equations explicitly; the monad
  derives congruence from application coherence.
- The outcome laws of
  [DivNonDetNE.v](../../../Code/Verification/Computation/DivNonDetNE.v): bind on
  `divnd`, absorption of divergence, blocking of the empty prefix, and bind
  on the two stacks.
- Shared structural equations in
  [RelArrowCoherence.v](../../../Code/Lib/Arrow/RelArrowCoherence.v), concrete property-only
  SP law packages in [SPostArr.v](../../../Code/SP/SPostArr.v) and
  [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v), and the existing
  relational laws in [Rel.v](../../../Code/Relational/Rel.v). All four relational SP
  readings reuse those `Rel` laws, rather than contributing duplicate packages.
- Constructive canonical ASP/DSLP normal forms and all four canonical SP law
  packages in [SPostArr.v](../../../Code/SP/SPostArr.v) and
  [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v), plus selected
  `CanonicalSP` interoperability clients in
  [ArrowMonadInstances.v](../../../Code/Tests/ArrowMonadInstances.v).
  The clients exercise canonical/compatibility application, bind dictionary
  identity, and state update followed by propagated failure. DSP/ASLP law
  packages retain classical relation recovery.
- `rel_state_option_bind` in
  [RelArrowCoherence.v](../../../Code/Lib/Arrow/RelArrowCoherence.v).
- Canonical ASP/DSLP fixed-input, state, option, and state-option relation
  readings in [SPostArr.v](../../../Code/SP/SPostArr.v). These wrappers
  specialize `rel_bind`, `relS_bind`, `relO_*`, and `relE_*` from
  [RelArrowCoherence.v](../../../Code/Lib/Arrow/RelArrowCoherence.v) through the existing
  `RelArrow` / `RelArrowChoice` / `RelArrowApply` dictionaries.
- DSP and ASLP under their pointwise orders, in
  [DSPMonad.v](../../../Code/SP/DSPMonad.v) and
  [ASLPMonad.v](../../../Code/SP/ASLPMonad.v): failure of the ordered
  monad laws with state and with exceptions, arbitrary-bind impossibility for
  Boolean state, and the ordered monads without state.
- The identification of the four directly defined stateless monads (`ASPSP`,
  `DSLPSP`, `DSPSP`, `ASLPSP`) with the arrow-derived ones: both morphism
  theorems and the ordered-monad instance of each.

- The triples development: monad morphisms and their transformer lifts,
  `arrow_morphism_monad`, the base arrow morphisms, the morphisms of
  [Verification/Triples/MonadMorphisms.v](../../../Code/Verification/Triples/MonadMorphisms.v) at three levels
  with both proofs of each SP morphism, the edges of
  [Verification/Triples/TripleTaxonomy.v](../../../Code/Verification/Triples/TripleTaxonomy.v) with state and with
  exceptions, the examples of [Verification/Triples/Examples.v](../../../Code/Verification/Triples/Examples.v),
  the rules of [Verification/Triples/InCorrectnessPrinciples.v](../../../Code/Verification/Triples/InCorrectnessPrinciples.v),
  and the construction, instances and triple identifications of
  [DijkstraMonad.v](../../../Code/Verification/DijkstraMonads/DijkstraMonad.v).
- The separation of the four healthiness classes in
  [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v).

The audit also reports the second adjunction between `PrePost` and `WPure`
and the generic option-order lift.

## Semantic regressions versus audit commands

The semantic regressions `empty_prefix_blocks` and `diverge_survives_empty`
live beside the computation laws in
[DivNonDetNE.v](../../../Code/Verification/Computation/DivNonDetNE.v). They are proofs
in the normal build; the audit also reports the first.

[SPostArrInfrastructure.v](../../../Code/Tests/SPostArrInfrastructure.v)
checks core, choice, and application laws for all four property-only flavours
without importing the SP monad files. Its semantic regressions distinguish DSP
composition from raw transformer composition and exercise non-unit
state-over-option bind. These checks are separate from the assumption reports.

## Build boundary and reading

`Assumptions.v` is deliberately absent from [_CoqProject](../../../Code/_CoqProject).
The maintained [Makefile](../../../Code/Makefile) keeps `all` as the default goal and
provides opt-in `make check`: it builds the normal build (the audit's
dependency closure lies inside it) and invokes Coq on the audit explicitly.
Its `clean` rule also removes audit outputs that ordinary `VFILES` cleanup
would miss.

Read `Assumptions.v` for the exact report selection and the `check` target
of [Makefile](../../../Code/Makefile) for execution membership. Consult the current output
for theorem dependencies rather than inferring them from imports. The target
reports assumptions; it does not compare them against an allowlist.

For direct-Rel equivalence results in
[SPostArrEquiv.v](../../../Code/SP/SPostArrEquiv.v), the public round trips,
morphisms, and operation-preservation results use the selected pointwise
equalities. The direct-Rel morphisms do not use Leibniz bridges. Loop-obstruction
transport in the same module has a separate local source-carrier equality step,
justified by property-only extensionality because arbitrary `ArrowLoop`
operations lack congruence; public obstruction statements remain semantic.
Use the audit source and its current output to determine which declarations
are reported and what assumptions they use.

Related contexts: [Lib](Lib.md),
[generic regressions](Tests.md), and
[concrete instance tests](Tests.md#concrete-arrow-instance-checks).
Those regression/instance checks belong to the normal build, unlike this audit.
