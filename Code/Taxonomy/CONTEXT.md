# Taxonomy context

Parent: [Code](../CONTEXT.md). Details: [README](README.md).
Source declarations and [_CoqProject](../_CoqProject) override older names.

## Ownership

- [ComputationMonads](ComputationMonads/CONTEXT.md) owns effects and outcomes.
  Its TransformerLaws is generic and also serves specification stacks.
- [BaseSpecMonads](BaseSpecMonads/CONTEXT.md) owns unary specifications,
  their properties, orders, and adjunctions. OldMonads holds the earlier
  healthy carriers; new public modules are arrow-derived four-flavour APIs.
- [Arrows](Arrows/CONTEXT.md) owns binary specification interfaces, concrete
  laws, and equivalence between canonical property-only SP arrows and plain
  `Rel`. The canonical SP carriers live in BaseSpecMonads. Check actual imports:
  the present dependency graph is not completely arrow-only.
- [EffectObservations](EffectObservations/CONTEXT.md) connects computations
  to specifications and compares observations/triples. SP and WP have separate
  outcome choices and directions. Arrow-derived clients coexist with old ones.
- ExampleProgramDefs shares programs without observations. InCorrectnessPrinciples
  states rewriting rules for the double-option tripleASP interface.
- [OldSP](OldSP/CONTEXT.md) retains some built earlier results;
  deprecated is excluded. Tests, examples, and assumption audits are distinct.

## Semantic cautions

None can mean exception, divergence, or structural failure depending on the
layer. For stdivexcnd, outer None is divergence and Some None is exception.
Terminating-slice observations can retain exceptions while omitting divergence;
full-outcome observations retain both layers where available.

Healthiness, monad equations, precondition monotonicity, and ordered bind
are separate. Pointwise DSP/ASLP ordered-bind counterexamples coexist with
relation-inclusion ordered monads. Over/Under SP and WP triples can reverse
implication and argument order: inspect the local definitions.

Read computation/outcomes → specification carrier/order → observation →
comparison/examples. A return/bind preservation theorem refers to the selected
source and target operations, not every similarly named dictionary.
