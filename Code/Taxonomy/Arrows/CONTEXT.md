# Specification arrows context

Parent: [Taxonomy](../CONTEXT.md). Related: [Classes](../../Classes/CONTEXT.md),
[base specifications](../BaseSpecMonads/CONTEXT.md), and [README](../README.md).

## Carriers

- The relational carrier in Rel.v is `A -> B -> Prop`, with existential
  composition and pointwise iff equality. Its fixed-input bind shares the
  input: `exists b, m i b /\ k b i c`. Option/state stacks are separate
  from unary PredM.Pred. Read its module for exact names during renames.
- PrePostArr pairs a precondition and an input-indexed post-relation;
  equality compares both by iff, while order reverses pre implication.
- SPArrT is the raw `(A -> Prop) -> B -> Prop`. Its monotone/strict/terminating/
  conjunctive/disjunctive properties do not supply a generic arrow instance.
  Conjunctive/disjunctive families are nonempty; strict/top preservation cover
  the empty cases where required.
- WPArr is a reader-WP Kleisli arrow over the raw WPureT, with Leibniz equality
  and reverse pointwise order. RelPrePostArr validates Hoare specs;
  project_wp compares operations/laws but not every raw validator verdict.

## SP presentations and monads

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

SPostArrMonad supplies selected generic dictionaries, recovered relations,
observation runners, and the ASP-to-DSLP monad map. Classes/ArrowMonad owns
generic return/bind and laws at arbitrary fixed input; unit-input clients
instantiate these rather than maintaining a duplicate generic implementation.
OptionLoop studies loop transport and obstructions separately from monad laws.
RelArrowCoherence derives application coherence from relational operation
semantics. Transformer law proofs are generic, not concrete carrier inspections.

Main's ASPArr/DSLPArr/DSPArr/ASLPArr in BaseSpecMonads are retained distinct
public bundles. ASP/DSLP and the property-only presentation now select
transformer iff, but the bundles are not definitionally equal because their
proof fields differ. Canonical-carrier consolidation is not yet done.
[OptionLoop.v](OptionLoop.v), `optionRel_no_left_tightening`, rules out lawful
`ArrowLoop` for the existing `optionRel` operations and pointwise equivalence
when feedback ranges over all types, including `Empty_set`. Empty feedback hides
the difference between an empty prefix and one returning `None`, while option
composition outside the loop distinguishes them. `SPostArrEquiv.v` transports
this obstruction to property-only option ASP and DSLP arrows. Its scope is this
unrestricted law and these operations, rather than every possible feedback design.
The no-lawful-loop corollaries bridge pointwise laws to the exact equalities
used by the transport theorem with `PureASPostArr_eq` / `PureDSLPostArr_eq`.

## Orders, boundaries, and clients

GaloisArr refines raw carriers as MonotoneWP, WFRelPrePost, and MonotoneSPost.
Preserve subtype hypotheses; a relation/SP adjunction does not identify every
monotone transformer with relational ASP. gamma_uni_not_monotone is an
obstruction; subsequent experimental commentary is not another theorem.

Relational modules can import computation semantics, and WPArr imports a base
specification module: distinguish ownership from the current import graph.
Read constructors → equality/laws → chosen monad dictionaries/orders →
[examples](Examples/CONTEXT.md) and [tests](Tests/CONTEXT.md).
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
