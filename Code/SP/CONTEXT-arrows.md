# Specification arrows context

Parent: [Taxonomy](../Taxonomy/CONTEXT.md). Related: [Classes](../Lib/CONTEXT.md),
[base specifications](CONTEXT.md), and [README](../Taxonomy/README.md).

## Carriers

- The relational carrier in Rel.v is `A -> B -> Prop`, with existential
  composition and pointwise iff equality. Its fixed-input bind shares the
  input: `exists b, m i b /\ k b i c`. Option/state stacks are separate
  from unary PredM.Pred. Read its module for exact names during renames.
- PrePostArr pairs a precondition and an input-indexed post-relation;
  equality compares both by iff, while order reverses pre implication.
- SPostArr.v defines the raw `SPArrT := (A -> Prop) -> B -> Prop` and its
  monotone/strict/terminating/conjunctive/disjunctive properties. The raw carrier
  has no generic arrow instance.
  Conjunctive/disjunctive families are nonempty; strict/top preservation cover
  the empty cases where required.
- WPArr is the WP Kleisli arrow over the raw WPureT, with Leibniz equality
  and reverse pointwise order. RelPrePostArr validates Hoare specs;
  project_wp compares operations/laws but not every raw validator verdict.

## SP presentations and monads

- [PredicateTransformerProperties.v](PredicateTransformerProperties.v) defines
  `StrictArr`, `TerminatingArr`, `DisjunctiveArr`, and `ConjunctiveArr` for forward
  transformers `(A -> Prop) -> B -> Prop`. The latter two preserve arbitrary
  **nonempty indexed families**; strictness supplies the empty join and termination
  the empty meet. `TerminatingArr` means **top preservation** here. See
  [PROPERTY_TERMINOLOGY.md](PROPERTY_TERMINOLOGY.md) for its semantic interpretation.
- [SPostArr.v](SPostArr.v) implements all four **property-only** binary carriers,
  their operations, normal forms, recovered relations, laws, stacks, and
  arrow-level conversions. It depends on Classes and arrow-owned helpers,
  not BaseSpecMonads. `ASPArr` / `DSLPArr` bundle monotonicity with
  strictness/disjunctivity or termination/conjunctivity; `DSPArr` / `ASLPArr`
  instead use strictness/conjunctivity or termination/disjunctivity.
  Compatibility aliases remain `PureASPostArr := ASPArr` and
  `PureDSLPostArr := DSLPArr`. Constructive `ASP_normal_form` /
  `DSLP_normal_form` recover relational readings without storing a relation;
  DSP/ASLP recovery is classical. DSP/ASLP operations split into ASP/DSLP parts,
  operate, then recombine by conjunction/disjunction. In particular, DSP
  composition is not raw forward transformer composition.
  `getASP` / `getDSLP` expose the ASP/DSLP transformers.
  `arrASP` / `arrDSLP` lift functions, with `arrASP_spec` / `arrDSLP_spec`
  exposing direct/universal images. `ASP_rel` / `DSLP_rel`, constructors
  `relASP` / `relDSLP`, their round trips, and relational rewrite facts all
  live in this arrow layer. `arrow_eq` is pointwise transformer iff;
  `PureASPostArr_eq` / `PureDSLPostArr_eq` separately recover bundled equality.
  The file ends with the separation of the four classes on one relation,
  `trueFromBoth`: its DSP reading is neither top-preserving nor disjunctive,
  its ASLP reading neither strict nor conjunctive, its DSLP reading not
  disjunctive, so none of them is the transformer of an arrow of the other
  kinds (`no_ASPArr_for_dsp`, `no_DSLPArr_for_dsp`, `no_ASPArr_for_aslp`,
  `no_DSLPArr_for_aslp`, `no_ASPArr_for_dslp`).
- The ASP singleton orientations remain distinct: canonical `aspRel` probes
  `fun x => x = a`, while `ASP_rel` probes `eq a` (`fun x => a = x`). Relate
  them by predicate equivalence, not definitional equality. The canonical and
  compatibility DSLP recovered relations are definitionally identical.
- [RelSPostArr.v](../Relational/RelSPostArr.v) computes four readings of the existing
  `Rel A B := A -> B -> Prop` carrier: `asp R P b := exists a, P a /\ R a b`
  and `dslp R P b := forall a, R a b -> P a`, with `dspOf` / `aslpOf` their
  conjunction/disjunction. `aspOf` / `dslpOf` are aliases of `asp` / `dslp`.
  The file owns the readings' healthiness, recovery, inclusion, and operation
  facts. The arrow value is the relation, not a relation/transformer pair or a
  new wrapper. At an unreachable output, ASP is false and DSLP is vacuously
  true; an empty input type has the same effect. Determinism alone does not
  identify these readings: a many-to-one
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
  `rel_reading_morphism` states the reading as a morphism into `Rel` for any
  arrow with faithful relational semantics, and `rel_section_morphism` does
  the same for a map back from relations that the reading inverts on the
  right; `dsp_to_rel_morphism` / `dsp_from_rel_morphism` and the ASLP pair
  instantiate them.
  The module aliases are `PropertySP := SPostArr` and `RelSP := RelSPostArr`.
  See the [README equivalence section](../Taxonomy/README.md#equivalence-with-rel) for
  the public option/state-over-option maps and their morphism theorems.

## Laws, stacks, and monads

All four canonical SP carriers provide `ArrowLaws`, `ArrowChoiceLaws`,
and `ArrowApplyLaws` by instantiating the shared semantic packages in
[RelArrowCoherence.v](../Lib/Arrow/RelArrowCoherence.v).
`RelArrow`, `RelArrowChoice`, and `RelArrowApply` describe operation preservation;
`RelArrowEq` connects the chosen equality to pointwise relation equivalence.
The ASP/DSLP compatibility interface exposes `ASP_rel` / `DSLP_rel`, with
operation facts phrased using the existing operators in `Rel.v`. Shared proofs supply
composition/first/choice congruence and `app_ext`, including replacement of
semantically equivalent arrows stored in inputs.
Relational-only helpers remain independent of equality reflection.

The relational presentation reuses `Arrow_Rel`, `ArrowChoice_Rel`,
`ArrowApply_Rel`, and their laws from [Rel.v](../Relational/Rel.v). Its selected equality is
`Rel_eq` (pointwise relation iff), not Leibniz equality. The existing
`optionRel` and `progRelArr` stacks serve all four SP readings; `RelSPostArr.v`
adds no carrier, arrow instance, or stack law package.

[ArrowMorphism.v](../Lib/Arrow/ArrowMorphism.v) lifts the direct-Rel morphisms
through option and state. The existing record takes explicit source and
destination `ArrowEq` dictionaries, requires `morphism_proper`, and states
its five preservation fields under the destination `arrow_eq`. Inverse and
lift proofs use the existing selected core/choice/application laws, not
Leibniz law dictionaries or relational equality reflection. See the
[Classes contract](../Lib/CONTEXT.md#contracts) for
the precise law requirements. All public base and lifted round trips retain
the selected semantic equalities.

`RelArrowCoherence.v` also owns `rel_bind`, `relS_bind`, `relO_*`, and `relE_*`
for base, state, option, and state-over-option normalization. These use the
existing `RelArrow` / `RelArrowChoice` / `RelArrowApply` contracts, without
arrow-law premises or equality reflection. [OptionArrowT.v](../Lib/Arrow/OptionArrowT.v) and
[StateArrowT.v](../Lib/Arrow/StateArrowT.v) lift the full contract generically.
The state-over-option stack maps `A * S` to `option (B * S)`; propagated `None`
carries no final state. On the property-only side, `ASPostArr S` /
`DSLPostArr S` fix its input to `unit`; the relational counterpart is
`progRelArr S`.

The unary monads of [ASPMonad.v](ASPMonad.v) and
[DSLPMonad.v](DSLPMonad.v) are these stacks, with
`Monad_ASPStExc` / `Monad_DSLPStExc` and the runners `getASPStExc` /
`getDSLPStExc`. They use the exact `Monad_Arrow` operations from
[ArrowMonad.v](../Lib/Arrow/ArrowMonad.v), whose laws hold for any fixed input
type under `ArrowLaws` and `ArrowApplyLaws`. Effects are stacked before fixing
the input. The binary `asp_to_dslp` conversion and its relation-reading facts
belong to `SPostArr.v`; the bridge proves its unit-input return/bind preservation.
The conversion changes the SP reading while preserving the recovered relation;
each property-only/`Rel` equivalence instead preserves its reading.

`ASPostArr` / `DSLPostArr` are definitionally the public `ASPStExc` /
`DSLPStExc` stacks. Compatibility dictionaries are plain definitions over
the canonical instances, avoiding competing registrations for equal aliases.
[Tests/SPostArrInfrastructure.v](../Tests/SPostArrInfrastructure.v) checks all four
flavours' law packages, the DSP composition distinction, and non-unit
state-over-option bind without importing BaseSpecMonads. `CanonicalSP` in
`Tests/ArrowMonadInstances.v` checks cross-API application/bind, dictionary and
runner identity, and propagated failure.

[OptionLoop.v](../Relational/OptionLoop.v), `optionRel_no_left_tightening`, rules out lawful
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

GaloisArr also hosts `MonoPT`, the MonotoneSPost carrier read with either
index fixed (first: SP; second: WP), and the three taxonomy relations on it:
`pt_le`, `Contrapositive`, and `GaloisPT`. `pt_under` / `pt_over` are the two
triple readings of a transformer. Contrapositive facts that turn a negated
statement back into a positive one are classical.

Relational modules can import computation semantics, and WPArr imports a base
specification module: distinguish ownership from the current import graph.
Read constructors → equality/laws → chosen monad dictionaries/orders →
[examples](../Tests/CONTEXT-examples.md) and [tests](../Tests/CONTEXT-arrows.md).
Start with the properties, then `SPostArr.v`, then the
[checked clients](../Tests/CONTEXT-examples.md); read `SPostArrEquiv.v` for representation
changes and [BaseSpecMonads/ASPMonad.v](ASPMonad.v) /
[DSLPMonad.v](DSLPMonad.v) for the unary monads.
For other carriers, [Rel.v](../Relational/Rel.v) defines relations,
[PrePostArr.v](../GaloisConnections/PrePostArr.v) pairs a precondition with an input-indexed
post-relation, and [RelPrePostArr.v](../GaloisConnections/RelPrePostArr.v) defines validators whose
arrow equality compares `project_wp` behavior.
[WPArr.v](../GaloisConnections/WPArr.v) uses raw `WPureT`, not the monotone `WPure` subset.
[GaloisArr.v](../GaloisConnections/GaloisArr.v) is the entrypoint for their refinement orders,
restricted adjunctions, and binary-arrow counterexamples.
