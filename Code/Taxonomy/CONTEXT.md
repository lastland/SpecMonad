# Taxonomy context

Parent: [Code](../CONTEXT.md). Details: [README](README.md).
Source declarations and [_CoqProject](../_CoqProject) override older names.

## Ownership

- [ComputationMonads](ComputationMonads/CONTEXT.md) owns effects and outcomes.
  Its TransformerLaws is generic and also serves specification stacks.
- [Arrows](Arrows/CONTEXT.md) owns binary specification interfaces, concrete
  laws, and ASP/DSLP equivalences with plain `Rel`. `SPostArr.v` implements all
  four property-only SP arrows, their binary stacks, and conversions without
  importing BaseSpecMonads. `Rel.v` owns relations; `RelSPostArr.v` owns their
  SP readings. Generic relational normalization belongs to Classes.
- [BaseSpecMonads](BaseSpecMonads/CONTEXT.md) owns unary specifications,
  their properties, orders, and adjunctions. The four public flavour monads
  consume `SPostArr.v`; `SPostArrMonad.v` supplies the unary observation bridge,
  and `SPure.v` supplies unary relational monads and orders. OldMonads holds
  the earlier healthy carriers.
- [EffectObservations](EffectObservations/CONTEXT.md) connects computations
  to specifications and compares observations/triples. SP and WP have separate
  outcome choices and directions. Arrow-derived clients coexist with old ones.
- [DijkstraMonads](DijkstraMonads/CONTEXT.md) indexes computations by observations
  and selected specification orders. It supplies WP and earlier ASP/DSLP SP
  clients, triple bridges, and selected-order sequencing/indexing obstructions.
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

For the property-only SP implementation, read Classes and arrow-owned helpers
→ SPostArr → BaseSpecMonads → observations. For an effect, read computation/outcomes
→ specification carrier/order → observation → comparison/examples. A return/bind
preservation theorem refers to the selected source and target operations, not
every similarly named dictionary.
