# Classes

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

This directory defines Hughes-style arrow contracts, generic transformer laws,
and constructions that consume those contracts. Concrete specification
carriers and their instances live in [Taxonomy arrows](../Taxonomy/Arrows/CONTEXT.md).
The pre/post-order classes in [Common](../Common/CONTEXT.md) are a separate API.

## Contracts and constructions

- [Arrow.v](Arrow.v) defines `Arrow` (`arr_pure`, `arr_comp`, `arr_first`),
  `ArrowEq`, `ArrowLaws`, and derived operations such as `arr_fanout`.
  `ArrowChoice`, `ArrowApply`, and `ArrowLoop` have separate law classes;
  `ArrowT` supplies transformer lifting.
- `ArrowApplyLaws` includes fixed-arrow application, `app_unit`,
  `app_precompose`, `app_postcompose`, and `app_ext`. The last field respects
  `arrow_eq` for arrows stored inside ordinary input values.
- [ArrowApplyFacts.v](ArrowApplyFacts.v) derives `arrow_ext` and `pure_ext`
  from arrow/application laws without assuming functional extensionality.
- [ArrowMonad.v](ArrowMonad.v) defines `ret_arrow`, `bind_arrow`, and
  `Monad_Arrow` for every fixed input `I`. Bind applies the selected
  continuation at that same input. `MonadLawsE_Arrow` uses the full application
  contract and the arrow's equality; `Eq1_Arrow` is an explicit dictionary,
  not a globally selected `Eq1` instance.
- [OptionArrowT.v](OptionArrowT.v) and [StateArrowT.v](StateArrowT.v) are public
  re-exports. Their [option](OptionArrowT/CONTEXT.md) and
  [state](StateArrowT/CONTEXT.md) subdirectories prove laws from base contracts
  without inspecting a concrete specification carrier.
- [ArrowMorphism.v](ArrowMorphism.v) uses an ordinary `ArrowMorphism` record
  with explicit dictionaries and Leibniz-equality preservation equations.
  Application preservation maps the embedded arrow in the input too.
  Inverse morphisms and option/state lifts reuse this record.
- [RelArrowCoherence.v](RelArrowCoherence.v) packages faithful relation
  semantics in `RelArrowPresentation`. It derives base application coherence
  and relational formulas including `rel_state_option_bind`; transformer
  application-law instances come from the generic transformer modules.
- [Galois.v](Galois.v) indexes `Galois` by both binary constructors and their
  orders, allowing different orders for the same carriers. It supplies the
  adjunction and derived monotonicity/inflation/deflation lemmas.

## Reading and boundaries

Start with `Arrow.v`, then `ArrowApplyFacts.v` and `ArrowMonad.v`, or the
transformer context relevant to the task. The concrete relational carrier is
`PredArr A B := A -> B -> Prop` in
[PredArr.v](../Taxonomy/Arrows/PredArr.v), not a definition in `Arrow.v`.

[Generic regressions](Tests/CONTEXT.md) protect the application contract and
generic monad-law resolution. [Concrete tests](../Taxonomy/Arrows/Tests/CONTEXT.md)
exercise actual Taxonomy carriers and transformer stacks.
All these Classes modules, including the regression, are in
[_CoqProject](../_CoqProject). Assumption reporting is a separate
[opt-in audit](../Checks/CONTEXT.md).
