# Specification arrows

Parent: [Taxonomy context](../CONTEXT.md). Related:
[Classes](../../Classes/CONTEXT.md), [base specification monads](../BaseSpecMonads/CONTEXT.md),
[SP observations](../EffectObservations/SP/CONTEXT.md),
[examples](Examples/CONTEXT.md), [concrete tests](Tests/CONTEXT.md).
The [taxonomy README](../README.md#8-arrows-vs-monads-file-split) gives the full architecture.

This directory defines binary specification carriers and their concrete arrow
laws. Generic arrow classes, transformer laws, and the arrow-to-monad construction
belong to `Classes/`; computation-specific interpretations belong to observations.

## SP carriers and well-formedness

- [PredicateTransformerProperties.v](PredicateTransformerProperties.v) defines
  `StrictArr`, `TerminatingArr`, `DisjunctiveArr`, and `ConjunctiveArr` for forward
  transformers `(A -> Prop) -> B -> Prop`. The latter two preserve arbitrary
  **nonempty indexed families**; strictness supplies the empty join and termination
  the empty meet. `TerminatingArr` means **top preservation** here. See
  [PROPERTY_TERMINOLOGY.md](PROPERTY_TERMINOLOGY.md) for its semantic interpretation.
- [SPostArr.v](SPostArr.v) is the **property-only** presentation:
  `PureASPostArr` bundles strictness and disjunctivity; `PureDSLPostArr` bundles
  termination and conjunctivity. `getASP` / `getDSLP` expose the transformer;
  operations act directly on it. `ASP_normal_form` / `DSLP_normal_form` recover
  relational readings without storing a relation in the carrier.
  `arrASP` / `arrDSLP` lift functions, with `arrASP_spec` / `arrDSLP_spec`
  exposing direct/universal images. `ASP_rel` / `DSLP_rel`, constructors
  `relASP` / `relDSLP`, their round trips, and relational rewrite facts all
  live in this arrow layer. `arrow_eq` is pointwise transformer iff;
  `PureASPostArr_eq` / `PureDSLPostArr_eq` separately recover bundled equality.
- [RelSPPairArr.v](RelSPPairArr.v) is the **coupled** presentation:
  `RelSPPair` stores `spost` and `rel`; `PureRelASPPairArr` / `PureRelDSLPPairArr`
  require their agreement with `asp` / `dslp`. ASP asks for some predecessor in
  the precondition; DSLP requires every predecessor to satisfy it. At an
  unreachable output ASP is false and DSLP is vacuously true. Determinism alone
  does not identify these readings: a many-to-one function can distinguish them.
- [SPostArrEquiv.v](SPostArrEquiv.v) proves both round trips for
  `asp_to_coupled` / `asp_from_coupled` and the DSLP counterparts. These maps
  preserve the transformer and all five operations: pure, composition, first,
  choice (`left`), and application. Application preservation also converts the
  arrow stored in the input. [ArrowMorphism.v](../../Classes/ArrowMorphism.v)
  supplies the exact option/state lifts, using explicit `*_leibniz` law
  dictionaries from `SPostArr.v`. Qualify shared names such as `ASPostArr`
  with `SPostArr` or `RelSPPairArr` when both presentations are imported.

## Laws, stacks, and monads

Both SP presentations provide `ArrowLaws`, `ArrowChoiceLaws`, and `ArrowApplyLaws`
by instantiating the shared semantic packages in
[RelArrowCoherence.v](../../Classes/RelArrowCoherence.v).
`RelArrow`, `RelArrowChoice`, and `RelArrowApply` describe operation preservation;
`RelArrowEq` connects the chosen equality to pointwise relation equivalence.
The property-only reading is `ASP_rel` / `DSLP_rel`, with operation facts phrased
using the existing operators in `Rel.v`. The coupled reading is
`rel (proj1_sig f)`, with definitional operation facts and its existing Leibniz
equality. Shared proofs supply composition/first/choice congruence and `app_ext`,
including replacement of semantically equivalent arrows stored in inputs.
Relational-only helpers remain independent of equality reflection.

`RelArrowCoherence.v` also supplies base application coherence and the
state-over-option relational bind formula. [OptionArrowT.v](../../Classes/OptionArrowT.v) and
[StateArrowT.v](../../Classes/StateArrowT.v) lift the full contract generically.
The state-over-option stack maps `A * S` to `option (B * S)`; propagated `None`
carries no final state. `ASPostArr S` / `DSLPostArr S` fix its input to `unit`.

[SPostArrMonad.v](SPostArrMonad.v) exposes the named `Monad_ASPostArr` /
`Monad_DSLPostArr` dictionaries and `runASP` / `runDSLP` for observations.
They use the exact `Monad_Arrow` operations from
[ArrowMonad.v](../../Classes/ArrowMonad.v), whose laws hold for any fixed input
type under `ArrowLaws` and `ArrowApplyLaws`. Effects are stacked before fixing
the input. `asp_to_dslp` preserves the recovered relation and return/bind while
changing its reading; the property-only/coupled conversions preserve the reading.

[OptionLoop.v](OptionLoop.v), `optionRel_no_left_tightening`, rules out lawful
`ArrowLoop` for the existing `optionRel` operations and pointwise equivalence
when feedback ranges over all types, including `Empty_set`. Empty feedback hides
the difference between an empty prefix and one returning `None`, while option
composition outside the loop distinguishes them. `SPostArrEquiv.v` transports
this obstruction to property-only option ASP and DSLP arrows. Its scope is this
unrestricted law and these operations, rather than every possible feedback design.
The no-lawful-loop corollaries bridge pointwise laws to the exact equalities
used by the transport theorem with `PureASPostArr_eq` / `PureDSLPostArr_eq`.

## Reading entrypoints

Start with the properties, then `SPostArr.v`, then the
[checked clients](Examples/CONTEXT.md); read `SPostArrEquiv.v` for representation
changes and `SPostArrMonad.v` for observation-facing use.
For other carriers, [Rel.v](Rel.v) defines relations,
[PrePostArr.v](PrePostArr.v) pairs a precondition with an input-indexed
post-relation, and [RelPrePostArr.v](RelPrePostArr.v) defines validators whose
arrow equality compares `project_wp` behavior.
[WPArr.v](WPArr.v) uses raw `WPureT`, not the monotone `WPure` subset.
[GaloisArr.v](GaloisArr.v) is the entrypoint for their refinement orders,
restricted adjunctions, and binary-arrow counterexamples.
