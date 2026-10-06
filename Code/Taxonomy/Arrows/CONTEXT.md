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
- [RelSPostArr.v](RelSPostArr.v) computes two readings of the existing
  `Rel A B := A -> B -> Prop` carrier: `asp R P b := exists a, P a /\ R a b`
  and `dslp R P b := forall a, R a b -> P a`. The arrow value is the relation,
  not a relation/transformer pair or a new wrapper. At an unreachable output
  ASP is false and DSLP is vacuously true; an empty input type has the same
  effect. Determinism alone does not identify these readings: a many-to-one
  function can distinguish them. The file retains `asp_inv` / `dslp_inv`,
  their recovery facts, and the DSP/ASLP characterizations.
- [SPostArrEquiv.v](SPostArrEquiv.v) uses `ASP_rel` / `relASP` and
  `DSLP_rel` / `relDSLP` directly, with round trips `asp_from_to` /
  `asp_to_from` and `dslp_from_to` / `dslp_to_from`. These use the selected
  property-only `arrow_eq` or `Rel_eq`, not ordinary equality. The maps
  preserve each transformer reading and all five operations: pure,
  composition, first, choice (`left`), and application, under the destination
  equality. Application preservation also converts the arrow stored in the
  input. The packaged morphisms are
  `asp_to_rel_morphism` / `asp_from_rel_morphism` and their DSLP counterparts.
  The module aliases are `PropertySP := SPostArr` and `RelSP := RelSPostArr`.
  See the [README equivalence section](../README.md#equivalence-with-rel) for
  the public option/state-over-option maps and their morphism theorems.

## Laws, stacks, and monads

The property-only ASP and DSLP carriers provide `ArrowLaws`, `ArrowChoiceLaws`,
and `ArrowApplyLaws` by instantiating the shared semantic packages in
[RelArrowCoherence.v](../../Classes/RelArrowCoherence.v).
`RelArrow`, `RelArrowChoice`, and `RelArrowApply` describe operation preservation;
`RelArrowEq` connects the chosen equality to pointwise relation equivalence.
The recovered relations are `ASP_rel` / `DSLP_rel`, with operation facts phrased
using the existing operators in `Rel.v`. Shared proofs supply
composition/first/choice congruence and `app_ext`, including replacement of
semantically equivalent arrows stored in inputs.
Relational-only helpers remain independent of equality reflection.

The relational presentation reuses `Arrow_Rel`, `ArrowChoice_Rel`,
`ArrowApply_Rel`, and their laws from [Rel.v](Rel.v). Its selected equality is
`Rel_eq` (pointwise relation iff), not Leibniz equality. The existing
`optionRel` and `progRelArr` stacks serve both SP readings; `RelSPostArr.v`
adds no carrier, arrow instance, or stack law package.

[ArrowMorphism.v](../../Classes/ArrowMorphism.v) lifts the direct-Rel morphisms
through option and state. The existing record takes explicit source and
destination `ArrowEq` dictionaries, requires `morphism_proper`, and states
its five preservation fields under the destination `arrow_eq`. Inverse and
lift proofs use the existing selected core/choice/application laws, not
Leibniz law dictionaries or relational equality reflection. See the
[Classes contract](../../Classes/CONTEXT.md#contracts-and-constructions) for
the precise law requirements. All public base and lifted round trips retain
the selected semantic equalities.

`RelArrowCoherence.v` also supplies base application coherence and the
state-over-option relational bind formula. [OptionArrowT.v](../../Classes/OptionArrowT.v) and
[StateArrowT.v](../../Classes/StateArrowT.v) lift the full contract generically.
The state-over-option stack maps `A * S` to `option (B * S)`; propagated `None`
carries no final state. On the property-only side, `ASPostArr S` /
`DSLPostArr S` fix its input to `unit`; the relational counterpart is
`progRelArr S`.

[SPostArrMonad.v](SPostArrMonad.v) exposes the named `Monad_ASPostArr` /
`Monad_DSLPostArr` dictionaries and `runASP` / `runDSLP` for observations.
They use the exact `Monad_Arrow` operations from
[ArrowMonad.v](../../Classes/ArrowMonad.v), whose laws hold for any fixed input
type under `ArrowLaws` and `ArrowApplyLaws`. Effects are stacked before fixing
the input. `asp_to_dslp` preserves the recovered relation and return/bind while
changing its reading; each property-only/`Rel` equivalence preserves its reading.

Main's ASPArr/DSLPArr/DSPArr/ASLPArr in BaseSpecMonads are retained distinct
public bundles. ASP/DSLP and the property-only presentation now select
transformer iff, but the bundles are not definitionally equal because their
proof fields differ. Canonical-carrier consolidation is not yet done.
[OptionLoop.v](OptionLoop.v), `optionRel_no_left_tightening`, rules out lawful
`ArrowLoop` for the existing `optionRel` operations and pointwise equivalence
when feedback ranges over all types, including `Empty_set`. Empty feedback hides
the difference between an empty prefix and one returning `None`, while option
composition outside the loop distinguishes them. `SPostArrEquiv.v` transports
this obstruction through the direct-Rel option maps to property-only option ASP
and DSLP arrows. Its scope is this unrestricted law and these operations,
rather than every possible feedback design.
The public `optionASP_no_left_tightening` / `optionDSLP_no_left_tightening`
theorems and `optionASP_no_lawful_ArrowLoop` / `optionDSLP_no_lawful_ArrowLoop`
corollaries use the property-only pointwise equalities.

The local loop transport uses existing property-only extensionality to turn
equivalence of recovered relations into equality of source arrows for one
substitution under the loop. This is needed because an arbitrary `ArrowLoop`
has no loop-congruence field. The projection-preservation facts remain
semantic; this local step neither reflects `Rel_eq` into equality of relations
nor changes the public obstruction's scope.

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
