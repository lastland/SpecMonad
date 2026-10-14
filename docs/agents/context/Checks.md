# Checks

Parent: [Code context](Code.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Purpose and audit scope

[Assumptions.v](../../../Code/Checks/Assumptions.v) is a console audit of selected proof
dependencies. It imports existing theorems and uses `Print Assumptions`
and `Check`; its output concerns only the named declarations. The audit
selects production declarations only: it imports no test or regression
module and reports no test or regression lemma, including regression lemmas
colocated with production code.

The selected reports cover:

- Core algebraic arrow helpers in [Arrow.v](../../../Code/Lib/Arrow/Arrow.v) and
  [ArrowApplyFacts.v](../../../Code/Lib/Arrow/ArrowApplyFacts.v), the fixed-input monad laws,
  and the option/state core, choice, and application law packages. The helpers
  obtain pure congruence from their core laws or take a fixed-arrow application
  equation explicitly. `lift_pure_proper` retains its separate source congruence
  premise without target laws. The audit also reports the shared relational
  core laws and equality-reflection transport, PrePost/RelPrePost/WP core laws.
- The outcome laws of
  [Computation.v](../../../Code/Verification/DivNonDet/Computation.v): bind on
  `divnd`, absorption of divergence, and bind on the two stacks.
- Shared structural equations in
  [RelArrowCoherence.v](../../../Code/Lib/Arrow/RelArrowCoherence.v), concrete property-only
  SP law packages in [SPostArr.v](../../../Code/SP/SPostArr.v) and
  [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v), and the existing
  relational laws in [Rel.v](../../../Code/Relational/Rel.v). All four relational SP
  readings reuse those `Rel` laws, rather than contributing duplicate packages.
- Constructive canonical ASP/DSLP normal forms and all four canonical SP law
  packages in [SPostArr.v](../../../Code/SP/SPostArr.v) and
  [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v). DSP/ASLP law
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
- Maillard's original `SPost` in [ASPMonad.v](../../../Code/SP/ASPMonad.v) and
  its supplied universal dual in [DSLPMonad.v](../../../Code/SP/DSLPMonad.v):
  their healthiness, inverse monad morphisms to ASP/DSLP at input `unit`, round
  trips, order equivalences, the dual's law and order packages, and the
  original monad's failure to preserve top.

- The triples development: monad morphisms and their transformer lifts,
  `arrow_morphism_monad`, the base arrow morphisms, the morphisms of
  [Verification/DivNonDet/Morphisms.v](../../../Code/Verification/DivNonDet/Morphisms.v) at three levels
  with both proofs of each SP morphism, the edges of
  [Verification/DivNonDetSt/TriplesTaxonomy.v](../../../Code/Verification/DivNonDetSt/TriplesTaxonomy.v) with state and with
  exceptions, the examples of [Verification/DivNonDetStExc/TriplesExamples/](../../../Code/Verification/DivNonDetStExc/TriplesExamples),
  the rules of [Verification/DivNonDetSt/InCorrectnessPrinciples.v](../../../Code/Verification/DivNonDetSt/InCorrectnessPrinciples.v),
  and the construction, instances and triple identifications of
  [DijkstraMonad.v](../../../Code/Verification/Generic/DijkstraMonad.v).
- The separation of the four healthiness classes in
  [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v).

The audit also reports the second adjunction between `PrePost` and `WPure`
and the generic option-order lift.

## Semantic regressions versus audit commands

The semantic regressions `empty_prefix_blocks` and `diverge_survives_empty`
live beside the computation laws in
[Computation.v](../../../Code/Verification/DivNonDet/Computation.v). They are proofs
in the normal build; the audit excludes both, and colocation with production
code does not bring a regression lemma into the audit.

[SPostArrInfrastructure.v](../../../Code/Tests/SPostArrInfrastructure.v)
checks core, choice, and application laws for all four property-only flavours
without importing the SP monad files. Its semantic regressions distinguish DSP
composition from raw transformer composition and exercise non-unit
state-over-option bind. These checks belong to the normal build and are
excluded from the assumption reports.

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
Those regression/instance checks belong to the normal build and are excluded
from this audit.
