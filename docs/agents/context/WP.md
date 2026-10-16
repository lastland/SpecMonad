# WP context

Parent: [Code](Code.md). Paper: Section 2 (WP monads) and Section 3.6
(the four WP monads). Consumers: [PTMonadTaxonomy](PTMonadTaxonomy.md),
[Triples](Verification.md), [DijkstraMonads](Verification.md),
[Galois connections](GaloisConnections.md).

- [WPure.v](../../../Code/WP/WPure.v): `WPureT` is the raw WP transformer and `WPure` its
  monotone subset, exposed by `getWPure`; `WSt S` and `WStExc S` stack state
  and optional exceptions over it by the ExtLib transformers. `WP_le` and its
  generic lifts `ordWSt` / `ordWStExc` are reverse implication;
  `OrderedMonad_WPure`, `OrderedMonad_WSt`, `OrderedMonad_WStExc` make them
  specification monads.
- [WPVariants.v](../../../Code/WP/WPVariants.v): AWP, DWLP, DWP, AWLP carved out of `WPure`
  by healthiness (`WPHealth`, `WPSub`), with state stacks and both orders.
  Each is a submonad of `WPure`; `OrderedMonad_WPSub` is
  `OrderedMonad_pullback` along `toWPure`.

| variant | conditions | reading |
|---|---|---|
| AWP | strict, disjunctive | some outcome satisfies the postcondition |
| DWLP | terminating, conjunctive | every outcome does |
| DWP | strict, conjunctive | every outcome does, and none diverges |
| AWLP | terminating, disjunctive | some outcome does, or one diverges |

[PTMonadTaxonomy](PTMonadTaxonomy.md) imports `WPVariants.v`. The monad
morphisms of [Triples](Verification.md) land in `WPure` itself; that each
lands in its variant is not proved
([wp-readings-soundness.md](../../notes/wp-readings-soundness.md)). Keep WP triple argument and direction
changes in mind: the orders are reverse implication.
