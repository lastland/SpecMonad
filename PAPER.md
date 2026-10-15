# Paper-to-code index

This file maps the claims of the submitted paper to the Rocq
development in [Code/](Code). It follows the paper's section order.

## Building and checking

```sh
cd Code
make -j
make check
```

`make check` also compiles [Code/Checks/PaperClaims.v](Code/Checks/PaperClaims.v),
which `Check`s every Rocq name in the tables below by its qualified name
(`File.name`, or `File.Module.name`). If a name is renamed or moved, that
file stops compiling. Unqualified names such as `WPure` or `stateArrT` in
the text are the paper's notation for the same objects. The axioms each main
result depends on are printed by
[Code/Checks/Assumptions.v](Code/Checks/Assumptions.v), which `make check`
also compiles. The development uses excluded middle, and functional and
propositional extensionality in places; that file says which results use
which.

Status column:

- **proved**: the claim is a closed theorem or definition in the build.
- **partial**: a weaker, more special, or differently shaped statement is
  proved; the row says how it differs.
- **not formalized**: no corresponding statement exists.

The paper's "Artifact:" lists use the file paths from before the
reorganization. [Old paths](#old-paths-in-the-papers-artifact-lists) at the
end of this file maps them to the current ones.

## Section 1: Introduction and contributions

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| Intro: "monotone *sps* alone do *not* form a lawful monad" | `MonotoneSPSt.SPStMonotone.AngelicMonotone.lunitStrictlyLax` | [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v) | proved, for monotone stateful transformers over an inhabited state type (take `S = unit` for the base case): left unit holds only as an inequation |
| Intro: the state monad transformer applied to the base *sp* monad has the shape `S -> P -> (A * S -> P)` | none (a statement about types) | | not formalized |
| Bullet 1: four lawful *sp* monads from arrows with application, extended by arrow transformers; four *wp* monads, all submonads of one | see Sections 3.2 to 3.6 | | proved |
| Bullet 2: taxonomy of the eight monads; preserved by monad and arrow transformers (state, exceptions) | see Section 4 | | partial: generic for monad transformers; for arrow transformers at the stacks used (base, `stateArrT`, `stateArrT` over `optionArrT`); Section 4.3 not formalized |
| Bullet 3: triples from monad morphisms out of the computation monad, lifted to state and exceptions; verified examples | `Computation.divndNE`; see Section 5 | [Verification/DivNonDet/Computation.v](Code/Verification/DivNonDet/Computation.v) | proved, except that the *wp* morphisms land in `WPure`, not in the four *wp* variants |
| Bullet 4: Dijkstra monads indexed by *asp*, *dslp*, and by *wp* with either order | see Section 6 | | proved; the *wp* Dijkstra monads are indexed by `WPure` and its stacks, not by the four variants |
| Bullet 5: *dsp*, *aslp* are lawful but not specification monads; under-approximate *asp* / over-approximate *dslp* orders differ from the triples; other triples are typings | see Section 6 | | proved; see [Gaps](#gaps-and-differences-from-the-paper) for the direction of "weaker" |
| Bullet 6: Galois connections with `Pred` and pre/postcondition pairs, the `Pred` ≅ `SPost` isomorphism extended to *asp* and *dslp*, preserved by transformers | see Section 7 | | partial: only the DM4All base adjunctions are proved |
| Bullet 7: "We mechanize all definitions and proofs in Rocq" | | | partial: see [Gaps](#gaps-and-differences-from-the-paper) |

## Section 2: Background, WP monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| `WPure A = (A -> P) -> P`, monotone, with the continuation `ret` / `bind`; monad laws | `WPure.WPure`, `WPure.MonadLawsE_WPure` | [WP/WPure.v](Code/WP/WPure.v) | proved |
| Pointwise order, `bind` monotone (an ordered monad) | `WPure.OrderedMonad_WPure`, `MonadTaxonomy.impliesWPure` | [WP/WPure.v](Code/WP/WPure.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved; `WP_le` is DM4All's reverse implication (`OrderedMonad_flip` gives the other direction); the paper's forward order is `impliesWPure` |
| `WSt` by the state monad transformer, monotone, ordered; with exceptions | `WPure.OrderedMonad_WSt`, `WPure.OrderedMonad_WStExc` | [WP/WPure.v](Code/WP/WPure.v) | proved |

## Section 3: SP monads

### 3.1 SPost: base *sp* monad

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| `SPost_ang`: Maillard et al.'s `SPost`, carrier `(pre : P) -> A -> {p \| p => pre}`, lawful | `SPostMonad.SPM.SPost`, `SPostMonad.SPMFacts.MonadLawsE_SPost`, `SPostMonad.OrderedMonad_SPost` | [SP/SPostMonad.v](Code/SP/SPostMonad.v) | proved |
| The same restriction on `P -> A -> P` (monotone + codomain) | `SPostMonad.SPostPure` | [SP/SPostMonad.v](Code/SP/SPostMonad.v) | proved (definition) |
| `SPost_dem`: universal `bind`, `ret v := a = v => pre`, lawful | `DSLPMonad.DSLPSP`, `DSLPMonad.monotone_codomainDSLP_iff_msingleton`, `DSLPMonad.dslpsp_to_dslp_morphism` | [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved, as `DSLPMonad.DSLPSP` (the direct stateless DSLP monad); there is no separate `SPost_dem` definition |

### 3.2 SPostArr: base *sp* arrow

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| An arrow with application, input type fixed, is a lawful monad (Lindley et al.) | `ArrowMonad.MonadLawsE_Arrow` | [Lib/Arrow/ArrowMonad.v](Code/Lib/Arrow/ArrowMonad.v) | proved |
| State arrow transformer `stateArrT`; it and the option transformer preserve the laws | `StateArrowT.Core.stateArrT`, `StateArrowT.ArrowApplyLaws.ArrowApplyLaws_stateArrT`, `OptionArrowT.ArrowApplyLaws.ArrowApplyLaws_optionArrT` | [Lib/Arrow/StateArrowT/](Code/Lib/Arrow/StateArrowT), [Lib/Arrow/OptionArrowT/](Code/Lib/Arrow/OptionArrowT) | proved |
| `SPostArr_ang` / `SPostArr_dem`: lawful angelic and demonic arrows | `SPostArr.ASPArr`, `SPostArr.ArrowApplyLaws_ASPArr`, `SPostArr.DSLPArr`, `SPostArr.ArrowApplyLaws_DSLPArr` | [SP/SPostArr.v](Code/SP/SPostArr.v) | partial: the lawful arrows are the Section 3.4 carriers (monotone + strict + disjunctive, monotone + terminating + conjunctive); the arrow restricted only by monotonicity and the codomain condition is not formalized, see [Gaps](#gaps-and-differences-from-the-paper) |
| "results in a lawful monad that is exactly `SPost_ang`" (resp. `SPost_dem`) | `ASPMonad.ASP`, `ASPMonad.ASPSP`, `ASPMonad.monotone_codomain_iff_singleton`, `ASPMonad.aspsp_to_asp_morphism`, `ASPMonad.asp_to_aspsp_morphism`, `DSLPMonad.dslpsp_to_dslp_morphism`, `DSLPMonad.dslp_to_dslpsp_morphism` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | partial: isomorphic, not equal; goes through the direct monads `ASPMonad.ASPSP` / `DSLPMonad.DSLPSP` on `P -> A -> P`, not through `SPostMonad.SPM.SPost` |

### 3.3 Correcting stateful SPostArr

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| Stateful angelic carrier (monotone, codomain): unit laws hold | `StatefulSPostCounterexample.SPostStExc`, `StatefulSPostCounterexample.SPostStExc_bind_ret_r`, `StatefulSPostCounterexample.SPostStExc_bind_ret_l` | [SP/StatefulSPostCounterexample.v](Code/SP/StatefulSPostCounterexample.v) | partial: hand-built carrier, see [Gaps](#gaps-and-differences-from-the-paper) |
| The `m`, `f`, `g` counterexample: `bind` is not associative | `StatefulSPostCounterexample.FailingBind.SPostStExc_bind_bind_fails`, `StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails` | [SP/StatefulSPostCounterexample.v](Code/SP/StatefulSPostCounterexample.v) | partial: angelic only, hand-built carrier |
| Demonic counterexample ("We can construct a similar counter-example") | none | | not formalized |
| Fix: universally disjunctive / conjunctive carriers | `SPostArr.asp_join_iff`, `SPostArr.dslp_meet_iff` | [SP/SPostArr.v](Code/SP/SPostArr.v) | proved |

### 3.4 Stateful ASP and DSLP

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| Universal disjunctivity = disjunctivity (inhabited index) + strictness; dually conjunctivity + termination | `PredicateTransformerProperties.strict_disjunctiveArr_full_join`, `PredicateTransformerProperties.terminating_conjunctiveArr_full_meet`, `SPostArr.asp_join_iff`, `SPostArr.dslp_meet_iff` | [SP/PredicateTransformerProperties.v](Code/SP/PredicateTransformerProperties.v), [SP/SPostArr.v](Code/SP/SPostArr.v) | proved |
| "for stateful monotone, disjunctive *sps*, the codomain condition is equivalent to strictness" (dually termination) | `ASPMonad.strict_to_singleton`, `ASPMonad.monotone_codomain_iff_singleton`, `DSLPMonad.monotone_codomainDSLP_iff_msingleton` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | partial: stateless only |
| `ASP S A` and `DSLP S A` are lawful monads | `ASPMonad.ASPSt`, `ASPMonad.MonadLawsE_ASPSt`, `DSLPMonad.MonadLawsE_DSLPSt` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved |

### 3.5 Stateful DSP and ASLP

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| DSP: conjunctive, strict; ASLP: disjunctive, terminating | `DSPASLPArr.DSPArr`, `DSPASLPArr.dsp_hom_iff`, `DSPASLPArr.ASLPArr`, `DSPASLPArr.aslp_hom_iff` | [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | proved |
| A DSP element is the conjunction of its `aspOf` and `dslpOf` components (ASLP: disjunction); `bind` through the components | `DSPASLPComponents.aspOfDSPArr`, `DSPASLPComponents.dslpOfDSPArr`, `DSPASLPComponents.aspOfASLPArr`, `DSPASLPComponents.dslpOfASLPArr`, `DSPASLPComponents.dsp_split_direct`, `DSPASLPComponents.aslp_split_direct`; `DSPASLPArr.aspPartArr`, `DSPASLPArr.dsp_split`, `DSPASLPArr.aslp_split` | [SP/DSPASLPComponents.v](Code/SP/DSPASLPComponents.v), [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | proved; `bind` goes through components computed from a recovered relation, see [Gaps](#gaps-and-differences-from-the-paper) |
| `DSP S A`, `ASLP S A` are lawful monads | `DSPMonad.MonadLawsE_DSPSt`, `ASLPMonad.MonadLawsE_ASLPSt` | [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved |
| The four classes differ (not stated in the paper) | `DSPASLPArr.no_ASPArr_for_dsp`, `DSPASLPArr.no_DSLPArr_for_aslp` | [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | proved |
| "`DSP A` is isomorphic to `ASP A` and `ASLP A` to `DSLP A`" | `DSPMonad.dsp_to_asp_morphism`, `DSPMonad.asp_to_dsp_morphism`, `ASLPMonad.aslp_to_dslp_morphism`, `ASLPMonad.dslp_to_aslp_morphism` | [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved |
| "`ASP A` is isomorphic to `SPost_ang A`", "`DSLP A` to `SPost_dem A`" | as in Section 3.2 | | partial, as in Section 3.2 |

### 3.6 WP monads of interpretations

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| `bind` of `WPure` preserves strict, terminating, conjunctive, disjunctive (and `ret` has all four) | `WPVariants.wpure_bind_strict`, `WPVariants.wpure_bind_terminating`, `WPVariants.wpure_bind_conjunctive`, `WPVariants.wpure_bind_disjunctive` | [WP/WPVariants.v](Code/WP/WPVariants.v) | proved |
| Four *wp* monads as submonads of `WPure`, ordered | `WPVariants.OrderedMonad_WPSub`, `OrderedMonad.OrderedMonad_SubMonad`, `WPVariants.OrderedMonad_DWLPSt`, `WPVariants.OrderedMonad_DWLPSt_op` | [WP/WPVariants.v](Code/WP/WPVariants.v), [Lib/Monad/OrderedMonad.v](Code/Lib/Monad/OrderedMonad.v) | proved (DWP, AWP, AWLP likewise, with and without state) |

## Section 4: Taxonomy (Figure 1)

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| 4.1: implication, contrapositive, Galois connection on bare transformers | `TransformerRelations.pt_le`, `TransformerRelations.Contrapositive`, `TransformerRelations.GaloisPT` | [PTMonadTaxonomy/TransformerRelations.v](Code/PTMonadTaxonomy/TransformerRelations.v) | proved |
| 4.2: monadic relation (DM4All); an ordered monad's order is one | `MonadRelation.MonadRelation`, `MonadRelation.MonadRelation_OrderedMonad` | [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v) | proved |
| Fig. 1b implication edges DWP→DWLP, DWP→AWP, AWP→AWLP, DWLP→AWLP | `MonadTaxonomy.MonadRelation_dwp_implies_dwlp`, `MonadTaxonomy.MonadRelation_dwp_implies_awp`, `MonadTaxonomy.MonadRelation_awp_implies_awlp`, `MonadTaxonomy.MonadRelation_dwlp_implies_awlp` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved (each also with its converse) |
| Fig. 1b implication edges DSP→ASP, DSP→DSLP, ASP→ASLP, DSLP→ASLP, through `aspOf` / `dslpOf` (the asterisks), each entailing `≤` of the elements | `MonadTaxonomy.MonadRelation_dsp_implies_asp`, `MonadTaxonomy.MonadRelation_dsp_implies_dslp`, `MonadTaxonomy.MonadRelation_asp_implies_aslp`, `MonadTaxonomy.MonadRelation_dslp_implies_aslp`, `MonadTaxonomy.dsp_implies_asp_part`, `MonadTaxonomy.asp_implies_aslp_part` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| Fig. 1 contrapositive edges DWLP–AWP, AWLP–DWP, ASP–DSLP, ASLP–DSP | `MonadTaxonomy.MonadRelation_contra_awp_dwlp_one`, `MonadTaxonomy.MonadRelation_contra_dwp_awlp_one`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_one`, `MonadTaxonomy.MonadRelation_contra_dsp_aslp_one` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved (each with a `_two` direction) |
| Fig. 1 Galois edges ASP → DWLP, AWP → DSLP | `MonadTaxonomy.MonadRelation_galois_asp_dwlp`, `MonadTaxonomy.MonadRelation_galois_awp_dslp` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| Fig. 1a: without state DSP coincides with ASP, ASLP with DSLP | `MonadTaxonomy.MonadRelation_dsp_asp_pure`, `MonadTaxonomy.MonadRelation_aslp_dslp_pure` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| 4.3 Category-theoretic insights | none | | not formalized (the section is empty in the paper) |
| 4.4 Effect-modularity: monadic relations lift through `stateT` / `optionT` | `MonadRelation.MonadRelation_stateT`, `MonadRelation.MonadRelation_optionT`, `MonadTaxonomy.MonadRelation_impliesWPure`, `MonadTaxonomy.MonadRelation_implies_WPSubStExc` | [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| 4.4: SP edges at any arrow-transformer stack; Galois edges from one `Pred` / `WPure` relation; instances without state and with exceptions | `MonadRelation.MonadRelation_rel_incl_state_option`, `MonadTaxonomy.MonadRelation_GaloisPredWP`, `MonadTaxonomy.MonadRelation_dsp_implies_asp_exc`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_pure`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_exc_one`, `MonadTaxonomy.MonadRelation_galois_asp_dwlp_pure`, `MonadTaxonomy.MonadRelation_galois_asp_dwlp_exc` | [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | partial: generic for monad transformers; for arrow transformers proved at the base, `stateArrT`, and `stateArrT` over `optionArrT` stacks, not for an arbitrary arrow transformer |

## Section 5: Triples

`Triple.Under` / `Triple.Over` name where the transformer sits (Section 4.1):
an `Under` triple puts the transformer's value in the conclusion
(`pre ⊆ wp post`, `post ⊆ sp pre`). So the Hoare triple `{p}c{q}` is
`dwlp Under` or, equivalently, `asp Over`, although the introduction calls
Hoare triples over-approximate.

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| Monad morphisms; lifting through monad transformers | `OrderedMonad.MonadMorphism`, `TransformerLaws.MonadMorphism_stateT`, `TransformerLaws.MonadMorphism_optionT` | [Lib/Monad/OrderedMonad.v](Code/Lib/Monad/OrderedMonad.v), [Lib/Monad/TransformerLaws.v](Code/Lib/Monad/TransformerLaws.v) | proved |
| Arrow morphisms; lifting through arrow transformers; to monad morphisms; the base arrow morphisms between the SP arrows and `Rel` | `ArrowMorphism.ArrowMorphism`, `ArrowMorphism.state_option_arrow_morphism`, `ArrowMorphism.arrow_morphism_monad`, `SPostArrEquiv.asp_to_rel_morphism`, `SPostArrEquiv.dslp_to_rel_morphism` | [Lib/Arrow/ArrowMorphism.v](Code/Lib/Arrow/ArrowMorphism.v), [SP/SPostArrEquiv.v](Code/SP/SPostArrEquiv.v) | proved |
| One triple for any monad morphism, under or over | `Triple.triple` | [Verification/Generic/Triple.v](Code/Verification/Generic/Triple.v) | proved (definition) |
| Morphisms from the computation monad into the four *wp* monads | `Morphisms.dwpPure_morphism`, `Morphisms.dwlpPure_morphism`, `Morphisms.awpPure_morphism`, `Morphisms.awlpPure_morphism` | [Verification/DivNonDet/Morphisms.v](Code/Verification/DivNonDet/Morphisms.v) | partial: they land in `WPure`, see [Gaps](#gaps-and-differences-from-the-paper) |
| Morphisms into the four *sp* monads | `Morphisms.aspPure_morphism_rel`, `Morphisms.dslpPure_morphism_rel`, `Morphisms.dspPure_morphism_rel`, `Morphisms.aslpPure_morphism_rel` | [Verification/DivNonDet/Morphisms.v](Code/Verification/DivNonDet/Morphisms.v) | proved |
| Lifted to state and exceptions "for free" | `Morphisms.dwpStExc_morphism`, `Morphisms.aspStExc_morphism_rel`, `Morphisms.dspStExc_morphism_rel` | [Verification/DivNonDetStExc/Morphisms.v](Code/Verification/DivNonDetStExc/Morphisms.v) | proved (all eight readings at both levels) |
| Incorrectness triple `[p]c[q]` as `q => asp [[c]] p` | `Triples.triple_aspSt` | [Verification/DivNonDetSt/Triples.v](Code/Verification/DivNonDetSt/Triples.v) | proved |
| The triple diagram (Verscht and Kaminski) for monadic programs | `TriplesTaxonomy.TotalCorr_impl_PartCorr`, `TriplesTaxonomy.DemIncorr_impl_IncorrLogic`, `TriplesTaxonomy.LisbonLogic_contra_dwlp_over`, `TriplesTaxonomy.IncorrLogic_contra_dslp_over`, `TriplesTaxonomy.PartCorr_galois_asp_over`, `TriplesTaxonomy.awp_over_galois_PartIncorr` | [Verification/DivNonDetSt/TriplesTaxonomy.v](Code/Verification/DivNonDetSt/TriplesTaxonomy.v) | proved (26 edges with state, again with exceptions) |
| One verified example per triple kind; O'Hearn's example | `ProgA.progA_dwp_under`, `ProgA.progA_asp_under`, `ProgEx.progEx_dslp_under`, `OHearn.example_incorrect` | [Verification/DivNonDetStExc/TriplesExamples.v](Code/Verification/DivNonDetStExc/TriplesExamples.v) and [TriplesExamples/](Code/Verification/DivNonDetStExc/TriplesExamples) | proved (16 kinds) |

## Section 6: Dijkstra monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| Specification monads stay so with the order flipped | `OrderedMonad.OrderedMonad_flip` | [Lib/Monad/OrderedMonad.v](Code/Lib/Monad/OrderedMonad.v) | proved |
| ASP and DSLP are specification monads | `ASPMonad.OrderedMonad_ASPSt`, `ASPMonad.OrderedMonad_ASPStExc`, `DSLPMonad.OrderedMonad_DSLPSt`, `DSLPMonad.OrderedMonad_DSLPStExc` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved (also without state) |
| DSP and ASLP: `bind` not monotone for the natural order, so not specification monads | `DSPMonad.not_OrderedMonad_DSPSt`, `ASLPMonad.not_OrderedMonad_ASLPSt`, `DSPMonad.dsp_arbitrary_bind_impossible` | [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved with state (and with exceptions); without state they are specification monads, `DSPMonad.OrderedMonad_DSP` |
| Dijkstra monad of a monad morphism, laws; eight WP and four SP Dijkstra monads | `DijkstraMonad.DM`, `DijkstraMonad.DMop`, `DijkstraMonad.DM_laws`, `DijkstraMonads.Dasp_laws` | [Verification/Generic/DijkstraMonad.v](Code/Verification/Generic/DijkstraMonad.v), [Verification/DivNonDetStExc/DijkstraMonads.v](Code/Verification/DivNonDetStExc/DijkstraMonads.v) | proved |
| Other triples are typings | `Typings.triple_under_wpStExc`, `Typings.triple_over_wpStExc`, `Typings.triple_over_aspStExc`, `Typings.triple_under_dslpStExc` | [Verification/DivNonDetStExc/Typings.v](Code/Verification/DivNonDetStExc/Typings.v) | proved |
| Under-approximate *asp* / over-approximate *dslp*: typing differs from the triple; no index characterizes the triple | `Typings.le_aspUnder`, `Typings.aspUnder_typing_triple`, `Typings.no_asp_under_index`, `Typings.no_dslp_over_index` | [Verification/Generic/Typings.v](Code/Verification/Generic/Typings.v), [Verification/DivNonDetSt/Typings.v](Code/Verification/DivNonDetSt/Typings.v) | proved; see [Gaps](#gaps-and-differences-from-the-paper) for "weaker" |
| Without state, ASP `Triple.Under` is a typing | `Typings.triple_under_aspPure` | [Verification/DivNonDet/Typings.v](Code/Verification/DivNonDet/Typings.v) | proved, for a precondition that holds |
| Typed example programs; a triple that is not a typing | `DijkstraExamples.progA_Ddwp`, `DijkstraExamples.progA_Dasp`, `DijkstraExamples.progEx_Ddslp_op`, `DijkstraExamples.progloom_harder_not_Dasp_op`, `Typings.oneOrTwo_Dasp_op` | [Verification/DivNonDetStExc/DijkstraExamples.v](Code/Verification/DivNonDetStExc/DijkstraExamples.v), [Verification/DivNonDet/Typings.v](Code/Verification/DivNonDet/Typings.v) | proved |

## Section 7: Galois connections between specification monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| DM4All's Galois connections between `Pred`, `PrePost`, `SPost`, `WPure` | `PredMonad.OrderedMonad_Pred`, `BaseGaloisConnections.pred_pp_adjunction`, `BaseGaloisConnections.wp_pp_under_adjunction`, `BaseGaloisConnections.sp_pp_adjunction` | [GaloisConnections/BaseGaloisConnections.v](Code/GaloisConnections/BaseGaloisConnections.v), [Relational/PredMonad.v](Code/Relational/PredMonad.v) | proved |
| Second WP / PrePost connection (paper: `NewGaloisConnections.v`) | `BaseGaloisConnections.wp_pp_over_adjunction` | [GaloisConnections/BaseGaloisConnections.v](Code/GaloisConnections/BaseGaloisConnections.v) | proved (classical) |
| `Pred` ≅ `SPost` extends to *asp* and *dslp* | nearest: `SPostArrEquiv.asp_to_rel_morphism`, `SPostArrEquiv.dslp_to_rel_morphism`, `SPostArr.asp_to_dslp`, `GaloisArr.Galois_Rel_SPost` | [SP/SPostArrEquiv.v](Code/SP/SPostArrEquiv.v), [SP/SPostArr.v](Code/SP/SPostArr.v), [GaloisConnections/GaloisArr.v](Code/GaloisConnections/GaloisArr.v) | not formalized |
| Galois connections hold after any monad or arrow transformer | nearest: `MonadTaxonomy.MonadRelation_GaloisPredWP` (Section 4) | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | not formalized |

## Gaps and differences from the paper

- **Section 7, contribution bullet 6.** Galois connections lifted through
  monad or arrow transformers are not formalized, and no Galois connection
  involves the new *sp* monads. The nearest result is the Section 4 one:
  `MonadTaxonomy.MonadRelation_GaloisPredWP`, the `Pred` / `WPure`
  adjunction as a monadic relation, lifted by the monad transformers on the
  WP side. The paper's Artifact list names `NewGaloisConnections.v`, which
  does not exist; `BaseGaloisConnections.wp_pp_over_adjunction` is in
  [GaloisConnections/BaseGaloisConnections.v](Code/GaloisConnections/BaseGaloisConnections.v).
- **No `Pred` ≅ `SPost` / ASP / DSLP isomorphism.** Nearest:
  `SPostArrEquiv.asp_to_rel_morphism` (ASP arrows are relations, as arrow
  isomorphisms), `SPostArr.asp_to_dslp` (an ASP arrow to the DSLP arrow of
  the same relation), and `GaloisArr.Galois_Rel_SPost` (relations and
  monotone SP transformers). None of these is stated for the unary monad
  `Pred`.
- **The WP morphisms land in `WPure`.** `Morphisms.dwpPure_morphism` and
  the other three map into `WPure`; no lemma shows that their image lies in
  DWP, DWLP, AWP or AWLP.
- **Section 3.3.** Only the angelic counterexample is formalized, and for the
  hand-built carrier `StatefulSPostCounterexample.SPostStExc` (stateful
  forward transformers restricted by monotonicity and the codomain
  condition), not literally for `stateArrT` over the angelic arrow at input
  `unit`. There is no demonic counterexample.
- **`SPost_ang`, `SPost_dem`.** `SPost_dem` is `DSLPMonad.DSLPSP` in
  [SP/DSLPMonad.v](Code/SP/DSLPMonad.v); there is no definition under that
  name. ASP ≅ `SPost_ang` goes through `ASPMonad.monotone_codomain_iff_singleton` (the
  carrier conditions agree) and `ASPMonad.aspsp_to_asp_morphism` (the direct
  monad is the arrow-derived one); no map is stated between `SPostMonad.SPM.SPost` and
  `ASP`.
- **Section 3.4.** "The codomain condition is equivalent to strictness" for
  stateful monotone disjunctive *sps* (and the demonic dual) is proved only
  without state (`ASPMonad.strict_to_singleton`,
  `ASPMonad.monotone_codomain_iff_singleton`, `DSLPMonad.monotone_codomainDSLP_iff_msingleton`).
  The stateful carriers are defined directly by strictness and
  disjunctivity, so the stateful equivalence is not needed by the
  construction.
- **Section 4.3** has no code.
- **Bullet 5, "weaker".** The paper says the under-approximate order on
  *asp* (and the over-approximate order on *dslp*) "correspond to strictly
  weaker specifications than the corresponding triples". In the code, a
  typing at the natural index (`Typings.le_aspUnder`) asks every start
  state in the precondition to reach every result in the postcondition. For
  an inhabited precondition it is strictly stronger than the triple
  (`Typings.aspUnder_typing_triple`; strictness by
  `Withdrawal.progloom_harder_asp_under` with
  `DijkstraExamples.progloom_harder_not_Dasp_op`); for an empty precondition
  it holds of every program, so it is vacuous. Neither "weaker" nor
  "stronger" holds uniformly; what holds for every index is that none has
  exactly the triples as its typings (`Typings.no_asp_under_index`).
  Dually for *dslp* Over: `Typings.dslpOver_typing_triple`,
  `DijkstraExamples.progloom_harder_dslp_over`,
  `DijkstraExamples.progloom_harder_not_Ddslp`,
  `Typings.no_dslp_over_index`. "Do not correspond to the triples" is
  the accurate wording.
- **Section 6 Artifact list: programs typed in the Dijkstra monad that cannot
  be typed with the triple** (ASP Under, DSLP Over) are not formalized. By
  `Typings.le_aspUnder` such a program can exist only for an empty
  precondition.
- **Section 3.2, `SPostArr_ang` / `SPostArr_dem`.** The arrows restricted only
  by monotonicity and the codomain condition are not defined; the lawful
  arrows in the code are the Section 3.4 carriers `SPostArr.ASPArr` and
  `SPostArr.DSLPArr`. Note for the paper: since `stateArrT` preserves the
  arrow laws for any lawful base arrow, a codomain-only arrow lawful at every
  input would make the Section 3.3 stateful monad lawful, so the Section 3.2
  claim can hold at most at input `unit`.
- **Admitted.** `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_bind` in
  [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v) is `Admitted`.
  Nothing uses it; the Galois edges are proved another way. It is the only
  `Admitted`, `admit` or `Abort` in the files of `_CoqProject` (an `admit`
  at line 552 of that file is inside a comment).
- **Section 3.5.** The paper defines `aspOf` / `dslpOf` on a whole
  precondition. These formulas are in
  [SP/DSPASLPComponents.v](Code/SP/DSPASLPComponents.v), but composition,
  and so `bind`, uses parts computed differently: the code first recovers
  a relation by probing with singleton complements (`DSPASLPArr.dspRel`
  relates `x` to `y` when `w (fun _ => True) y /\ ~ w (fun z => z <> x) y`,
  the paper's `aspOf` formula at precondition `x`), then takes its ASP and
  DSLP readings (`DSPASLPArr.aspPartArr`). The two agree
  (`DSPASLPComponents.aspOfDSP_aspPart`,
  `DSPASLPComponents.dslpOfDSP_dslpPart`,
  `DSPASLPComponents.aspOfASLP_aspPartA`,
  `DSPASLPComponents.dslpOfASLP_dslpPartA`). The recovery and the
  agreement are classical.

## Beyond the paper

- [Relational/OptionLoop.v](Code/Relational/OptionLoop.v): no lawful
  `ArrowLoop` for the option-relation arrow
  (`OptionLoop.optionRel_no_lawful_ArrowLoop`), transported to the option ASP
  and DSLP arrows (`SPostArrEquiv.optionASP_no_lawful_ArrowLoop`).
- `InCorrectnessPrinciples.v` in [Generic/](Code/Verification/Generic/InCorrectnessPrinciples.v) and in each setting ([DivNonDet/](Code/Verification/DivNonDet/InCorrectnessPrinciples.v), [DivNonDetSt/](Code/Verification/DivNonDetSt/InCorrectnessPrinciples.v), [DivNonDetStExc/](Code/Verification/DivNonDetStExc/InCorrectnessPrinciples.v)):
  O'Hearn's rewriting rules (symmetry, consequence, agreement, denial) for
  the ASP triples at each setting, with demonic liberal WP variants (e.g.
  `InCorrectnessPrinciples.principle_of_denial_asp` with state). The rules are proved once for the ASP reading of any relation and instantiated at each setting; the demonic liberal WP variants go through each setting's Galois edge (without state, `PartCorr_galois_asp_over_pure` in `DivNonDet/TriplesTaxonomy.v`).
- [GaloisConnections/GaloisArr.v](Code/GaloisConnections/GaloisArr.v):
  Galois connections between binary specification arrows (relations,
  pre/post pairs, monotone SP and WP transformers, relational pre/post
  validators), e.g. `GaloisArr.Galois_RPP_WP`.
- [PTMonadTaxonomy/SPStBindComparisons.v](Code/PTMonadTaxonomy/SPStBindComparisons.v):
  the stateful SP `bind`s compared with the angelic and demonic `bind`s of
  monotone stateful transformers (`SPStBindComparisons.bindASPSt_angelic`).
- The four SP healthiness classes are pairwise distinct
  (`DSPASLPArr.no_ASPArr_for_dsp`, `DSPASLPArr.no_DSLPArr_for_aslp`).
- Programs as interaction trees ([Verification/DivNonDet/Computation.v](Code/Verification/DivNonDet/Computation.v),
  [Lib/ITreeFacts.v](Code/Lib/ITreeFacts.v)): an `itree E A` over events that all have an answer
  (`HasAnswers`) is denoted into the computation monad (`denote`; with state
  `denoteSt`, with state and exceptions `denoteStExc`), a monad morphism up to
  `eutt`, so the readings of a program are those of its denotation
  (`dwpPure ∘ₘₘ denote` &c.). Examples in each setting's
  `TriplesExamples/ITreePrograms.v`.

## Old paths in the paper's Artifact lists

| Paper path | Current path |
|---|---|
| `BaseSpecMonads/SPostMonad.v` | [SP/SPostMonad.v](Code/SP/SPostMonad.v) (`SPost`) and [SP/StatefulSPostCounterexample.v](Code/SP/StatefulSPostCounterexample.v) (the stateful counterexample) |
| `Classes/Arrow.v`, `Classes/ArrowMonad.v`, `Classes/ArrowMorphism.v` | [Lib/Arrow/](Code/Lib/Arrow) |
| `Classes/StateArrowT/*`, `Classes/OptionArrowT/*` | [Lib/Arrow/StateArrowT/](Code/Lib/Arrow/StateArrowT), [Lib/Arrow/OptionArrowT/](Code/Lib/Arrow/OptionArrowT) |
| `Classes/MonadRelation.v`, `Classes/OrderedMonad.v` | [Lib/Monad/](Code/Lib/Monad) |
| `Taxonomy/ComputationMonads/TransformerLaws.v` | [Lib/Monad/TransformerLaws.v](Code/Lib/Monad/TransformerLaws.v) |
| `Taxonomy/Arrows/PredicateTransformerProperties.v`, `Taxonomy/Arrows/SPostArrEquiv.v` | [SP/](Code/SP) |
| `Taxonomy/Arrows/SPostArr.v` | [SP/SPostArr.v](Code/SP/SPostArr.v) (ASP, DSLP) and [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) (DSP, ASLP) |
| `{ASP,DSLP,DSP,ASLP}Monad.v` | [SP/](Code/SP) |
| `Taxonomy/BaseSpecMonads/MonadTaxonomy.v` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) (Figure 1 edges, `Section Flavours`) and [PTMonadTaxonomy/Carriers.v](Code/PTMonadTaxonomy/Carriers.v) |
| `Taxonomy/BaseSpecMonads/WPureMonad.v` | [WP/WPure.v](Code/WP/WPure.v) and [WP/WPVariants.v](Code/WP/WPVariants.v) |
| `Taxonomy/Triples/*` (including `MonadMorphism.v`, meaning `MonadMorphisms.v`) | split by setting under [Verification/](Code/Verification): the morphisms in `DivNonDet/Morphisms.v`, `DivNonDetSt/Morphisms.v`, `DivNonDetStExc/Morphisms.v`; the triples in `Generic/Triple.v` and `*/Triples*.v`; the diagram in `*/TripleTaxonomy*.v`; the examples in `DivNonDetStExc/TriplesExamples/`; the rules in `DivNonDetSt/InCorrectnessPrinciples.v` |
| `Taxonomy/DijkstraMonads/*` | [Verification/Generic/DijkstraMonad.v](Code/Verification/Generic/DijkstraMonad.v) (the construction) and `Dijkstra*.v` / `Typings*.v` per setting |
| `Taxonomy/BaseSpecMonads/BaseGaloisConnections.v` | [GaloisConnections/BaseGaloisConnections.v](Code/GaloisConnections/BaseGaloisConnections.v) |
| `Taxonomy/BaseSpecMonads/NewGaloisConnections.v` | does not exist; see Section 7 |
