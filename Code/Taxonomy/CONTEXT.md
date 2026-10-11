# Taxonomy context

Parent: [Code](../CONTEXT.md). Details: [README](README.md).
Source declarations and [_CoqProject](../_CoqProject) override older names.

## Ownership

- [ComputationMonads](../Computation/CONTEXT.md) owns effects and outcomes.
  Its TransformerLaws is generic and also serves specification stacks.
- [Arrows](../SP/CONTEXT-arrows.md) owns binary specification interfaces, concrete
  laws, and ASP/DSLP equivalences with plain `Rel`. `SPostArr.v` implements all
  four property-only SP arrows, their binary stacks, and conversions without
  importing BaseSpecMonads. `Rel.v` owns relations; `RelSPostArr.v` owns their
  SP readings. Generic relational normalization belongs to Classes.
- [BaseSpecMonads](../SP/CONTEXT.md) owns unary specifications,
  their properties, orders, and adjunctions. The four public flavour monads
  consume `SPostArr.v`, and `SPure.v` supplies unary relational monads and
  orders.
- [Triples](../Triples/CONTEXT.md) defines monad morphisms out of `divndNE` and
  its `stateT` / `optionT` stacks, lifts their triples, and proves the
  taxonomy diagram with state and with state and exceptions. It also holds
  the examples and O'Hearn's rewriting rules. The maps are not called
  observations: the DSP and ASLP targets are not specification monads.
- [DijkstraMonads](../Dijkstra/CONTEXT.md) gives the Dijkstra monad of any
  monad morphism into an ordered monad, instantiates it at every morphism of
  Triples, and identifies triples with typings where that is exact.
- Tests, examples, and assumption audits are distinct.

## Semantic cautions

None can mean exception, divergence, or structural failure depending on the
layer. With state and exceptions over `divndNE`, outer None is divergence and
Some None is an exception. The SP morphisms read the terminating outcomes:
they keep exceptions and omit divergence.

Healthiness, monad equations, precondition monotonicity, and ordered bind
are separate. DSP and ASLP are not specification monads: their `bind` is not
monotone for their order. Over/Under SP and WP triples can reverse
implication and argument order: inspect the local definitions.

For the property-only SP implementation, read Classes and arrow-owned helpers
→ SPostArr → BaseSpecMonads → Triples. For an effect, read computation/outcomes
→ specification carrier/order → morphism → diagram/examples. A return/bind
preservation theorem refers to the selected source and target operations, not
every similarly named dictionary.
