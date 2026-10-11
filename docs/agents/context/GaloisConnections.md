# Galois connections context

Parent: [Code](Code.md). Paper: Section 7 (Galois connections between
specification monads).

## The DM4All specification monads (unary)

- [PrePostMonad.v](../../../Code/GaloisConnections/PrePostMonad.v): `PPM.PrePost` pairs a propositional
  precondition with a result predicate; bind checks continuations universally
  and collects results existentially. `PP_le` and `OrderedMonad_PrePost` are
  at the end of the file.
- [RelPrePostMonad.v](../../../Code/GaloisConnections/RelPrePostMonad.v): validators into `Assuming pre`,
  whose propositions satisfy `q <-> (pre -> q)`, with Hoare-order
  monotonicity. `MR_le` and `OrderedMonad_RelPrePost` are at the end.
- [BaseGaloisConnections.v](../../../Code/GaloisConnections/BaseGaloisConnections.v) relates the unary
  presentations through their orders: `Pred -| PrePost`, both adjunctions
  between `PrePost` and `WPure` (the second, `wp_pp_over_adjunction`, is the
  one the paper's artifact list attributes to a nonexistent
  `NewGaloisConnections.v`), `WPure -| RelPrePost`, `SPost -| PrePost`
  (an impredicative intersection), `SPost -| RelPrePost`, with unit and
  counit. `Pred` is in [Relational/PredMonad.v](../../../Code/Relational/PredMonad.v),
  `SPost` in [SP/SPostMonad.v](../../../Code/SP/SPostMonad.v).

Not formalized: the paper's claim that these connections survive monad and
arrow transformers. The nearest result is the monadic-relation lifting of
`GaloisPredWP` in [PTMonadTaxonomy/MonadTaxonomy.v](../../../Code/PTMonadTaxonomy/MonadTaxonomy.v).

## Binary arrows (beyond the paper)

- [PrePostArr.v](../../../Code/GaloisConnections/PrePostArr.v) pairs a precondition and an input-indexed
  post-relation; equality compares both by iff, while order reverses pre
  implication.
- [WPArr.v](../../../Code/GaloisConnections/WPArr.v) is the WP Kleisli arrow over the raw `WPureT` (not the
  monotone `WPure`), with Leibniz equality and reverse pointwise order.
- [RelPrePostArr.v](../../../Code/GaloisConnections/RelPrePostArr.v) validates Hoare specs; `project_wp`
  compares operations/laws but not every raw validator verdict.
- [GaloisArr.v](../../../Code/GaloisConnections/GaloisArr.v) refines the raw carriers as `MonotoneWP`,
  `WFRelPrePost` and `MonotoneSPost` (the last defined in
  [PTMonadTaxonomy/TransformerRelations.v](../../../Code/PTMonadTaxonomy/TransformerRelations.v)) and
  proves `Galois_Rel_PrePost`, `Galois_Rel_SPost`, `Galois_WP_PrePost`,
  `Galois_RPP_WP`. Preserve subtype hypotheses: a relation/SP adjunction does
  not identify every monotone transformer with relational ASP.
  `gamma_uni_not_monotone` is an obstruction; the commentary after it is not
  another theorem.
