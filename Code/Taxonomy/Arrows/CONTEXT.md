# Specification arrows context (main)

Parent: [Taxonomy context](../CONTEXT.md).
Related: [base specification monads](../BaseSpecMonads/CONTEXT.md) and
[generic arrow classes](../../Classes/Arrow.v).

## Purpose and scope

This directory defines binary specification carriers and their concrete arrow
laws. Main's SP arrows store both a transformer and a relation. Read the actual
definitions, not older comments that refer to separate facts files or unary names.

## Carriers and equivalences

- [PredArr.v](PredArr.v): `PredArr A B = A -> B -> Prop`, relational
  composition, and `Pred_eq` as pointwise iff. Its fixed-input monad uses
  `bindPred m k a c = exists b, m a b /\ k b a c`, sharing the input `a`.
  `optionPred`, `progPredArr` / `nditPredArr`, and `progPredM` / `nditPredM`
  provide option/state presentations. This is not unary `PredM.Pred`.
- [PrePostArr.v](PrePostArr.v): `PrePostArr A B` pairs `A -> Prop` with
  `A -> B -> Prop`. The post-relation retains the initial input; `PrePost_eq`
  compares both components by iff. `PrePost_le` reverses the precondition
  implication and preserves the post-relation implication.
- [SPArr.v](SPArr.v): `SPArrT A B = (A -> Prop) -> B -> Prop`, the raw SP
  transformers, with the homomorphism properties `sp_monotone`, `sp_strict`,
  `sp_terminating`, `sp_conjunctive`, and `sp_disjunctive` (the last two over
  nonempty families). `MonotoneSPost` and the SP arrows of
  [BaseSpecMonads](../BaseSpecMonads/CONTEXT.md#sp-arrows) are subset types of
  it. It has no arrow instance: the refinements' operations differ.
- [WPArr.v](WPArr.v): `WPArr A B = A -> WPureT B`, using the raw carrier
  imported from [WPureMonad.v](../BaseSpecMonads/WPureMonad.v), not its monotone
  `WPure` subset. `ArrowEq_WPArr` uses Leibniz equality; `WPArr_le` uses reverse
  pointwise implication. Its homomorphism properties `wp_monotone`,
  `wp_terminating` (top preservation), and `wp_conjunctive` (nonempty
  families) mirror `SPArr.v`. `MonotoneWP` and the meet-preserving `DWLPArr`
  of [DWLPArrowCore.v](../BaseSpecMonads/DWLPArrowCore.v) are subset types of it.
- [RelPrePostArr.v](RelPrePostArr.v): `RelPrePostArr A B` validates
  preconditions and input-indexed post-relations. Operations and arrow/monad
  equivalence use `project_wp`. That equivalence does not compare every raw
  validator verdict; `RelPrePost_le` separately orders raw verdicts in reverse.

## SP arrows and monad views

[SPostArr.v](SPostArr.v) defines `SPRecord` with fields `sp_pt` and `sp_rel`.
`PureASPostArr` requires their agreement with `asp`; `PureDSLPostArr` requires
agreement with `dslp`. Constructors `mkASP` / `mkDSLP` package a relation.
For a relation `R`, `asp R pre b` asks for a predecessor satisfying `pre`,
whereas `dslp R pre b` requires every predecessor to satisfy `pre`.
An unreachable output makes ASP false and DSLP true.

Both SP arrow equivalences are Leibniz equality. `PureASPostArr_eq` /
`PureDSLPostArr_eq` recover bundled equality from transformer iff;
`IsASP_rewrite` / `IsDSLP_rewrite` expose relational readings.
`ASPostArr S A` and `DSLPostArr S A` apply state over option arrows, then fix
the input to `unit`: their base input is `unit * S`, output `option (A * S)`.

`Section ArrowMonad` in the same file defines `ret_arrow`, `bind_arrow`, and
`Monad_Arrow` for a fixed input and `ArrowApply`. The concrete
`MonadLawsE_PureASPostArr` / `MonadLawsE_PureDSLPostArr` declarations use the
direct `Monad_PureASPostArr` / `Monad_PureDSLPostArr` dictionaries. Do not read
these as a generic law theorem for every `Monad_Arrow` instance.

`Section ArrowMonadLaws` that follows it IS the generic theorem, but only at
input `unit`: `MonadLawsE_Arrow` proves `MonadLawsE` for `Monad_Arrow arr unit`
from `ArrowLaws` + `ArrowApplyLaws`, with `Eq1_Arrow` = `arrow_eq`. The
restriction to `unit` is what makes `bind_arrow`'s fanout collapse
(`bind_arrow_unit`); at a general input the input must be threaded and the
laws do not follow from the fields the class has. Specification monads
presented as arrows at input `unit` (see `BaseSpecMonads/ASPArrow.v`) take
their `MonadLawsE` from here rather than proving it by hand.

`Section ArrowMorphismMonad` then shows that an arrow morphism preserving
`arr_app` ([ArrowMorphism.v](../../Classes/ArrowMorphism.v)) preserves
`ret_arrow` and `bind_arrow` at every input, not only `unit`
(`morph_ret_arrow`, `morph_bind_arrow`).

## Boundaries and comparison results

- Generic option/state arrow laws live in [OptionArrowT.v](../../Classes/OptionArrowT.v)
  and [StateArrowT.v](../../Classes/StateArrowT.v). The arrow-to-monad
  construction above still lives here, not in a separate generic module.
- Main's `PredArr.v` imports [StDivITree.v](../ComputationMonads/StDivITree.v),
  and `WPArr.v` imports a base-specification file. Distinguish semantic
  independence from the current import graph.
- [GaloisArr.v](GaloisArr.v) defines `MonotoneWP` (`WPArr` refined by
  `wp_monotone`), `WFRelPrePost`, and
  `MonotoneSPost` (`SPArrT` refined by `sp_monotone`), then `Galois_Pred_PrePost`, `Galois_Pred_SPost`,
  `Galois_WP_PrePost`, and `Galois_RPP_WP`. Preserve their subtype hypotheses.
  The relation/SP adjunction does not identify every monotone transformer with
  a relational ASP. `gamma_uni_not_monotone` is a stated obstruction;
  the subsequent existential-variant discussion is commentary, not another theorem.
  These connect specification carriers. The Galois connection of one program,
  asp ⊣ dwlp, is a relation between two arrows instead, in
  [GaloisTranspose.v](../BaseSpecMonads/GaloisTranspose.v).

## Reading order

Start with `PredArr.v`, then the chosen carrier and its equality. Read
`SPostArr.v`'s constructors before its law proofs or monad dictionaries.
Use `GaloisArr.v` for binary orders and adjunctions, and
[effect observations](../EffectObservations/CONTEXT.md) for computation-specific use.
