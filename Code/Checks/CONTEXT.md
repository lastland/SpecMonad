# Checks

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and audit scope

[Assumptions.v](Assumptions.v) is a console audit of selected proof
dependencies. It imports existing theorems and uses `Print Assumptions`
and `Check`; its output concerns only the named declarations.

The selected reports cover:

- Core algebraic arrow helpers in [Arrow.v](../Classes/Arrow.v) and
  [ArrowApplyFacts.v](../Classes/ArrowApplyFacts.v), the fixed-input monad laws,
  and the option/state core, choice, and application law packages. The helpers
  obtain pure congruence from their core laws or take a fixed-arrow application
  equation explicitly. `lift_pure_proper` retains its separate source congruence
  premise without target laws. The audit also reports the shared relational
  core laws and equality-reflection transport, PrePost/RelPrePost/WP core laws,
  and the exact-equality `WrongIndex` regression's core laws.
- The outcome laws of
  [DivNonDetNE.v](../Taxonomy/ComputationMonads/DivNonDetNE.v): bind on
  `divnd`, absorption of divergence, blocking of the empty prefix, and bind
  on the two stacks.
- Shared structural equations in
  [RelArrowCoherence.v](../Classes/RelArrowCoherence.v), concrete property-only
  SP law packages in [SPostArr.v](../Taxonomy/Arrows/SPostArr.v), and the existing
  relational laws in [Rel.v](../Taxonomy/Arrows/Rel.v). All four relational SP
  readings reuse those `Rel` laws, rather than contributing duplicate packages.
- Constructive canonical ASP/DSLP normal forms and all four canonical SP law
  packages in [SPostArr.v](../Taxonomy/Arrows/SPostArr.v), plus selected
  `CanonicalSP` interoperability clients in
  [ArrowMonadInstances.v](../Taxonomy/Arrows/Tests/ArrowMonadInstances.v).
  The clients exercise canonical/compatibility application, bind dictionary
  identity, and state update followed by propagated failure. DSP/ASLP law
  packages retain classical relation recovery.
- `rel_state_option_bind` in
  [RelArrowCoherence.v](../Classes/RelArrowCoherence.v).
- Canonical ASP/DSLP fixed-input, state, option, and state-option relation
  readings in [SPostArr.v](../Taxonomy/Arrows/SPostArr.v). These wrappers
  specialize `rel_bind`, `relS_bind`, `relO_*`, and `relE_*` from
  [RelArrowCoherence.v](../Classes/RelArrowCoherence.v) through the existing
  `RelArrow` / `RelArrowChoice` / `RelArrowApply` dictionaries.
- DSP and ASLP under their pointwise orders, in
  [DSPMonad.v](../Taxonomy/BaseSpecMonads/DSPMonad.v) and
  [ASLPMonad.v](../Taxonomy/BaseSpecMonads/ASLPMonad.v): failure of the ordered
  monad laws with state and with exceptions, arbitrary-bind impossibility for
  Boolean state, and the ordered monads without state.
- The identification of the four directly defined stateless monads (`ASPSP`,
  `DSLPSP`, `DSPSP`, `ASLPSP`) with the arrow-derived ones: both morphism
  theorems and the ordered-monad instance of each.

- The triples development: monad morphisms and their transformer lifts,
  `arrow_morphism_monad`, the base arrow morphisms, the morphisms of
  [Triples/MonadMorphisms.v](../Taxonomy/Triples/MonadMorphisms.v) at three levels
  with both proofs of each SP morphism, the edges of
  [Triples/Diagram.v](../Taxonomy/Triples/Diagram.v) with state and with
  exceptions, the examples of [Triples/Examples.v](../Taxonomy/Triples/Examples.v),
  the rules of [Triples/InCorrectnessPrinciples.v](../Taxonomy/Triples/InCorrectnessPrinciples.v),
  and the construction, instances and triple identifications of
  [DijkstraMonad.v](../Taxonomy/DijkstraMonads/DijkstraMonad.v).
- The separation of the four healthiness classes in
  [SPostArr.v](../Taxonomy/Arrows/SPostArr.v).

The audit also reports the second adjunction between `PrePost` and `WPure`
and the generic option-order lift.

## Semantic regressions versus audit commands

The semantic regressions `empty_prefix_blocks` and `diverge_survives_empty`
live beside the computation laws in
[DivNonDetNE.v](../Taxonomy/ComputationMonads/DivNonDetNE.v). They are proofs
in the normal build; the audit also reports the first.

[SPostArrInfrastructure.v](../Taxonomy/Arrows/Tests/SPostArrInfrastructure.v)
checks core, choice, and application laws for all four property-only flavours
without importing BaseSpecMonads. Its semantic regressions distinguish DSP
composition from raw transformer composition and exercise non-unit
state-over-option bind. These checks are separate from the assumption reports.

## Build boundary and reading

`Assumptions.v` is deliberately absent from [_CoqProject](../_CoqProject).
The maintained [Makefile](../Makefile) keeps `all` as the default goal and
provides opt-in `make check`: it builds the normal build (the audit's
dependency closure lies inside it) and invokes Coq on the audit explicitly.
Its `clean` rule also removes audit outputs that ordinary `VFILES` cleanup
would miss.

Read `Assumptions.v` for the exact report selection and the `check` target
of [Makefile](../Makefile) for execution membership. Consult the current output
for theorem dependencies rather than inferring them from imports. The target
reports assumptions; it does not compare them against an allowlist.

For direct-Rel equivalence results in
[SPostArrEquiv.v](../Taxonomy/Arrows/SPostArrEquiv.v), the public round trips,
morphisms, and operation-preservation results use the selected pointwise
equalities. The direct-Rel morphisms do not use Leibniz bridges. Loop-obstruction
transport in the same module has a separate local source-carrier equality step,
justified by property-only extensionality because arbitrary `ArrowLoop`
operations lack congruence; public obstruction statements remain semantic.
Use the audit source and its current output to determine which declarations
are reported and what assumptions they use.

Related contexts: [Classes](../Classes/CONTEXT.md),
[generic regressions](../Classes/Tests/CONTEXT.md), and
[concrete Taxonomy tests](../Taxonomy/Arrows/Tests/CONTEXT.md).
Those regression/instance checks belong to the normal build, unlike this audit.
