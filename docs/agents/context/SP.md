# SP context

Parent: [Code](Code.md). Paper: Section 3.1-3.5 (strongest
postcondition monads). Builds on [Lib](Lib.md) and
[Relational](Relational.md); used by
[PTMonadTaxonomy](PTMonadTaxonomy.md), [Triples](Verification.md),
[DijkstraMonads](Verification.md). Source declarations determine exact
types, selected dictionaries and orders. Qualify shared names, especially
unary accessors such as `ASPMonad.getASP` against the binary
`SPostArr.getASP` (and likewise for DSLP).

## Terminology

[PROPERTY_TERMINOLOGY.md](../../PROPERTY_TERMINOLOGY.md#sp-presentation-terminology)
defines **Maillard's SP monad**, its supplied **demonic variant**
(`SPost_dem`, the DSLP variant), **monotone SP arrow**, and **healthy SP arrow**.
The monotone arrow presentations require only monotonicity; the healthy
ASP/DSLP arrows also bundle their respective class conditions. Healthiness and
algebraic arrow/monad laws remain distinct.

## Files in paper order

| Paper | File | Contents |
|---|---|---|
| 3.1 | [SPostMonad.v](../../../Code/SP/SPostMonad.v) | `SPM.SPost`: monotone transformers into `Over pre` (propositions implying the precondition), `SP_le`, `OrderedMonad_SPost`; `SPostPure`, the same restriction on raw transformers, and its conditions `Monotone`, `Codomain`, `CodomainDSLP` used by the ASP and DSLP files |
| 3.3 | [StatefulSPostCounterexample.v](../../../Code/SP/StatefulSPostCounterexample.v) | `SPostStExc` and `St.SPostSt`: stateful carriers restricted like `SPost`; `FailingBind`: the m/f/g counterexample to associativity. Hand-built carriers, not literally `stateArrT` over the angelic arrow; only the angelic case |
| 3 | [RawSP.v](../../../Code/SP/RawSP.v) | raw `SPPure`, `SPSt`, `SPStExc`, the terminating slice `StTrans`, the order on raw transformers. Not the carriers of the four monads |
| 3.3-3.4 | [PredicateTransformerProperties.v](../../../Code/SP/PredicateTransformerProperties.v) | `StrictArr`, `TerminatingArr`, `DisjunctiveArr`, `ConjunctiveArr` for `(A -> Prop) -> B -> Prop`; see [PROPERTY_TERMINOLOGY.md](../../PROPERTY_TERMINOLOGY.md) |
| 3.2, 3.4 | [SPostArr.v](../../../Code/SP/SPostArr.v) | the raw `SPArrT` and its properties; the ASP and DSLP arrows, normal forms, recovered relations, laws, stacks, `asp_to_dslp` |
| 3.5 | [DSPASLPArr.v](../../../Code/SP/DSPASLPArr.v) | the DSP and ASLP arrows, their stacks, and the separation of the four classes |
| 5 | [SPostArrEquiv.v](../../../Code/SP/SPostArrEquiv.v) | ASP/DSLP/DSP/ASLP arrows as morphisms to and from `Rel`; the transported `ArrowLoop` obstruction |
| 3.4-3.5 | [ASPMonad.v](../../../Code/SP/ASPMonad.v), [DSLPMonad.v](../../../Code/SP/DSLPMonad.v), [DSPMonad.v](../../../Code/SP/DSPMonad.v), [ASLPMonad.v](../../../Code/SP/ASLPMonad.v) | the four SP monads at input `unit`, with state and with state and exceptions; `ASPMonad.v` and `DSLPMonad.v` also connect `SPM.SPost` and the universal dual `SPostDem.SPost` to `ASP` and `DSLP` at input `unit`, prove their healthiness, and record the top-preservation counterexample |

## The arrows

`ASPArr` / `DSLPArr` bundle monotonicity with strictness/disjunctivity or
termination/conjunctivity; `DSPArr` / `ASLPArr` use strictness/conjunctivity
or termination/disjunctivity. Conjunctive/disjunctive families are nonempty;
strictness supplies the empty join and termination (top preservation) the
empty meet. The carriers hold transformers and healthiness proofs, not stored
relations. The arrow files depend on Lib, Relational and
`PredicateTransformerProperties.v` (and `DSPASLPArr.v` on `SPostArr.v`), never
on the monad files.

- ASP/DSLP have constructive normal forms (`ASP_normal_form` /
  `DSLP_normal_form`); DSP/ASLP recover relations classically. DSP/ASLP
  operations split into ASP and DSLP parts, operate, then recombine by
  conjunction/disjunction; DSP composition is not raw transformer
  composition.
- `getASP` / `getDSLP` expose transformers; `arrASP` / `arrDSLP` lift
  functions (`arrASP_spec` / `arrDSLP_spec`). `ASP_rel` / `DSLP_rel`, the
  constructors `relASP` / `relDSLP`, their round trips and rewrite facts are
  in the arrow layer. `arrow_eq` is pointwise transformer iff;
  `PureASPostArr_eq` / `PureDSLPostArr_eq` recover bundled equality.
  Compatibility aliases: `PureASPostArr := ASPArr`, `PureDSLPostArr := DSLPArr`.
- The canonical `aspRel` probes `fun x => x = a`, `ASP_rel` probes `eq a`:
  relate them by predicate equivalence, not definitional equality.
- All four carriers provide `ArrowLaws`, `ArrowChoiceLaws`, `ArrowApplyLaws`
  by instantiating the shared packages of
  [RelArrowCoherence.v](../../../Code/Lib/Arrow/RelArrowCoherence.v). The state-over-option
  stack maps `A * S` to `option (B * S)`; a propagated `None` carries no final
  state. `ASPostArr S` / `DSLPostArr S` fix its input to `unit`.
- `DSPASLPArr.v` ends with `trueFromBoth`: its DSP reading is neither
  top-preserving nor disjunctive, its ASLP reading neither strict nor
  conjunctive, its DSLP reading not disjunctive (`no_ASPArr_for_dsp`,
  `no_DSLPArr_for_dsp`, `no_ASPArr_for_aslp`, `no_DSLPArr_for_aslp`,
  `no_ASPArr_for_dslp`).
- [SPostArrEquiv.v](../../../Code/SP/SPostArrEquiv.v): `asp_from_to` / `asp_to_from` and the
  DSLP pair use the selected `arrow_eq` or `Rel_eq`, not ordinary equality.
  The maps preserve each reading and all five operations; application
  preservation also converts the arrow stored in the input. Packaged as
  `asp_to_rel_morphism` / `asp_from_rel_morphism` and their DSLP
  counterparts; `rel_reading_morphism` / `rel_section_morphism` give the
  DSP/ASLP pairs. Module aliases: `PropertySP := SPostArr`,
  `RelSP := RelSPostArr`. `optionASP_no_left_tightening` /
  `optionDSLP_no_left_tightening` transport the obstruction of
  [OptionLoop.v](../../../Code/Relational/OptionLoop.v); the local loop transport uses
  property-only extensionality for one substitution under the loop.

## The monads

Each monad file fixes input `unit` and uses the generic
[ArrowMonad.v](../../../Code/Lib/Arrow/ArrowMonad.v) operations and laws; effects are
stacked before fixing the input. Each exposes pure/state/state-option
monads, runners, refinement orders, ordered-bind proofs, and ends with the
stateless monad defined directly on `SPPure A = Prop -> A -> Prop`: `ASPSP`
(`Singleton`), `DSLPSP` (`MSingleton`), `DSPSP` / `ASLPSP`, with operations
suffixed `SP` (`retASPSP`, `bindASPSP`, `getASPSP`). `aspsp_to_asp` /
`asp_to_aspsp` and the three analogous pairs show each direct monad is the
arrow-derived one. There is no direct definition with state.
`ASPMonad.v` connects the original `SPM.SPost` to `ASP` through `ASPSP`, and
`DSLPMonad.v` defines the supplied universal carrier `SPostDem.SPost` and
connects it to `DSLP` through `DSLPSP`. The maps preserve readings, `ret`,
`bind`, and orders, and their round trips use pointwise iff. Hence neither
carrier excludes healthy values at input `unit`. The angelic chain is
constructive; the demonic law and equivalence proofs use excluded middle.
`SPostDem.OrderedMonad_SPost` itself is constructive.
`dm4all_not_dslp_healthy` shows that the original existential monad does not
generally preserve top. These base equivalences do not assert an equivalence
for arbitrary binary inputs or state stacks.

`DSPMonad.v` and `ASLPMonad.v` close with the pure collapse: at input `unit`
the DSP and ASP conditions coincide, and so do the ASLP and DSLP ones;
`dsp_to_asp` / `asp_to_dsp` and `aslp_to_dslp` / `dslp_to_aslp` are the
identity on transformers, mutually inverse, and preserve `ret`, `bind` and the
pointwise orders (only ASP-to-DSP is constructive). `OrderedMonad_DSP` /
`OrderedMonad_ASLP` pull back the ASP / DSLP orders. They also refute the
ordered monad laws with state (`not_OrderedMonad_DSPSt`,
`not_OrderedMonad_ASLPSt`, and the `StExc` pair) and prove
`dsp_arbitrary_bind_impossible` / `aslp_arbitrary_bind_impossible` for
Boolean state. The monad laws still hold.

| monad | order | ordered? |
|---|---|---|
| `SPM.SPost` | `SP_le` | yes |
| `ASP`, `ASPSt S`, `ASPStExc S`, `ASPSP` | pointwise (follows relation inclusion) | yes |
| `DSLP`, `DSLPSt S`, `DSLPStExc S`, `DSLPSP` | pointwise (reverses it) | yes |
| `DSP`, `DSPSP` / `ASLP`, `ASLPSP` | pointwise | yes |
| `DSPSt S`, `DSPStExc S` / `ASLPSt S`, `ASLPStExc S` | pointwise | no |

The canonical `ASPStExc` / `DSLPStExc` are definitionally the compatibility
`ASPostArr` / `DSLPostArr` stacks of `SPostArr.v`. That an ASP element and the
DSLP element denoting the same relation correspond under `ret` and `bind` is
`MonadRelation_contra_asp_dslp_exc_one` / `_two` in
[MonadTaxonomy.v](../../../Code/PTMonadTaxonomy/MonadTaxonomy.v).

Read: properties → `SPostArr.v` → `DSPASLPArr.v` → a monad file; the
[checked clients](Tests.md) exercise the public operations.
