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
(`File.name`, `Dir.File.name` where several files share a name, or
`File.Module.name`). The tables are generated from that file: one row per
claim, in paper order, with the line of the claim in the paper's source. If a name is renamed or moved, that
file stops compiling. Unqualified names such as `WPure` or `stateArrT` in
the text are the paper's notation for the same objects. The axioms each main
result depends on are printed by
[Code/Checks/Assumptions.v](Code/Checks/Assumptions.v), which `make check`
also compiles. The development uses excluded middle, and functional and
propositional extensionality in places, and the interaction-tree layer
`eq_rect_eq` (through ITree and paco); that file says which results use
which.

Status column:

- **proved**: the claim is a closed theorem or definition in the build.
- **partial**: a weaker, more special, or differently shaped statement is
  proved; the row says how it differs.
- **not checkable**: a claim about the development as a whole (its size,
  its axioms); the row says how it stands.

The paper's source (comments and unrendered draft notes) names file paths
from before the reorganization. [Old paths](#old-paths-in-the-papers-source)
at the end of this file maps them to the current ones.

## Section 1, Introduction

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.427-439: partial correctness is `p => dwlp c q`, equivalently `asp c p => q`; incorrectness logic is `q => asp c p` (for monadic stateful programs; `PartCorr`, `IncorrLogic` are the named triples). | `DivNonDetSt.TriplesTaxonomy.PartCorr_galois_asp_over`, `DivNonDetSt.Triples.triple_aspSt` | [Verification/DivNonDetSt/TriplesTaxonomy.v](Code/Verification/DivNonDetSt/TriplesTaxonomy.v), [Verification/DivNonDetSt/Triples.v](Code/Verification/DivNonDetSt/Triples.v) | proved |
| l.469-473: the state transformer on the wp monad. | `WPure.WSt`, `WPure.MonadLawsE__WSt` | [WP/WPure.v](Code/WP/WPure.v) | proved |
| l.479: "monotone sps alone do not form a lawful monad". | `MonotoneSPSt.SPStMonotone.AngelicMonotone.lunitStrictlyLax` | [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v) | partial: for the angelic structure on monotone stateful transformers, left unit holds only as an inequation; the converse fails for an inhabited state |
| l.483: Maillard et al.'s `SPost` specifies programs under the angelic, total interpretation: it is isomorphic to `ASP` as a monad. | `ASPMonad.dm4all_to_asp_morphism`, `ASPMonad.asp_to_dm4all_morphism`, `ASPMonad.dm4all_round_trip`, `ASPMonad.asp_dm4all_round_trip` | [SP/ASPMonad.v](Code/SP/ASPMonad.v) | proved |
| l.490-496: the four homomorphism properties of sps. | `PredicateTransformerProperties.StrictArr`, `PredicateTransformerProperties.TerminatingArr`, `PredicateTransformerProperties.ConjunctiveArr`, `PredicateTransformerProperties.DisjunctiveArr` | [SP/PredicateTransformerProperties.v](Code/SP/PredicateTransformerProperties.v) | proved |
| l.568-573: a specification monad is a monad ordered so that `bind` is monotone. | `OrderedMonad.OrderedMonad` | [Lib/Monad/OrderedMonad.v](Code/Lib/Monad/OrderedMonad.v) | proved |
| l.639-641: the base computation monad of nondeterminism and nontermination. | `DivNonDet.Computation.divndNE` | [Verification/DivNonDet/Computation.v](Code/Verification/DivNonDet/Computation.v) | proved |
| l.643-644: state and exceptions on both sides; the morphisms lift for free. | `Monad.TransformerLaws.MonadMorphism_optionT`, `ArrowMorphism.state_option_arrow_morphism`, `DivNonDetStExc.Morphisms.dwpStExc_morphism`, `DivNonDetStExc.Morphisms.aspStExc_morphism_rel`, `DivNonDetStExc.Morphisms.dspStExc_morphism_rel` | [Lib/Monad/TransformerLaws.v](Code/Lib/Monad/TransformerLaws.v), [Lib/Arrow/ArrowMorphism.v](Code/Lib/Arrow/ArrowMorphism.v), [Verification/DivNonDetStExc/Morphisms.v](Code/Verification/DivNonDetStExc/Morphisms.v) | proved |
| l.650-653: simple programs proved to satisfy correctness and incorrectness triples, and O'Hearn's example (all sixteen kinds: Section 7). | `ProgA.progA_dwp_under`, `ProgA.progA_asp_under`, `ProgEx.progEx_dslp_under`, `OHearn.example_incorrect` | [Verification/DivNonDetStExc/TriplesExamples/ProgA.v](Code/Verification/DivNonDetStExc/TriplesExamples/ProgA.v), [Verification/DivNonDetStExc/TriplesExamples/ProgEx.v](Code/Verification/DivNonDetStExc/TriplesExamples/ProgEx.v), [Verification/DivNonDetStExc/TriplesExamples/OHearn.v](Code/Verification/DivNonDetStExc/TriplesExamples/OHearn.v) | proved |
| l.655-656: asp, dslp and all wp monads are specification monads, also with exceptions; l.662: flipping the order covers over- and under-approximation. | `ASPMonad.OrderedMonad_ASPStExc`, `DSLPMonad.OrderedMonad_DSLPStExc`, `WPure.OrderedMonad_WStExc`, `OrderedMonad.OrderedMonad_flip` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v), [WP/WPure.v](Code/WP/WPure.v), [Lib/Monad/OrderedMonad.v](Code/Lib/Monad/OrderedMonad.v) | proved |
| l.668-670: the dsp and aslp binds are not monotone. l.672-679: which triples embed in Dijkstra monads (the bullet swaps asp and dslp; the artifact and Section 5 agree that asp over and dslp under embed, asp under and dslp over do not); backed in Section 5. | `DSPMonad.not_OrderedMonad_DSPSt`, `ASLPMonad.not_OrderedMonad_ASLPSt` | [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | partial: with state only; without state DSP and ASLP coincide with ASP and DSLP, see Section 4.2 |
| l.738-742: Galois connections with stateful `Pred` (Section 6) and pre/post specifications. | `GaloisArr.Galois_Rel_PrePost`, `GaloisArr.Galois_WP_PrePost` | [GaloisConnections/GaloisArr.v](Code/GaloisConnections/GaloisArr.v) | partial: as Galois connections of binary arrows, at input [S] |
| l.740-748: the isomorphism between `Pred` and `SPost` extends to isomorphisms between asp and dwlp and between dslp and awp as stateful specification monads. | `MonadTaxonomy.galois_asp_dwlp_order`, `MonadTaxonomy.galois_awp_dslp_order`, `PredIsomorphisms.pred_to_dm4all_morphism` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [SP/PredIsomorphisms.v](Code/SP/PredIsomorphisms.v) | partial: order isomorphisms, compatible with the monad structure, through the Galois relations; see Section 6 |

## Section 2, Background: weakest precondition monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.799-813: the monotone continuation monad on `P`, with its `ret` and `bind`; l.840-866: monotonicity, preserved by `ret` and `bind`. | `WPure.WPure`, `WPure.wpure_mono`, `WPure.retWPure`, `WPure.bindWPure`, `WPure.MonadLawsE_WPure`, `WPVariants.wpure_ret_mono`, `WPVariants.wpure_bind_mono` | [WP/WPure.v](Code/WP/WPure.v), [WP/WPVariants.v](Code/WP/WPVariants.v) | proved |
| l.868-876: the pointwise order, preserved by `ret` and `bind` (`WP_le` is DM4all's direction, the converse of the paper's). | `WPure.WP_le`, `WPure.OrderedMonad_WPure` | [WP/WPure.v](Code/WP/WPure.v) | proved |
| l.886-913: the stateful wp monad, ordered, with monotone `bind`. | `WPure.retPs`, `WPure.bindPs`, `WPure.ordWSt`, `WPure.OrderedMonad_WSt` | [WP/WPure.v](Code/WP/WPure.v) | proved |

## Section 3.1, Base sp monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.1080-1082: an sp of a pure program, `P -> (A -> P)`. | `RawSP.SPPure` | [SP/RawSP.v](Code/SP/RawSP.v) | proved |
| l.1088-1108: Maillard et al.'s `SPost` (monotone, postconditions imply the precondition), with (ang) `ret`/`bind`, is lawful. | `SPostMonad.SPM.SPost`, `SPostMonad.SPM.retSP`, `SPostMonad.SPM.bindSP`, `SPostMonad.SPMFacts.MonadLawsE_SPost`, `SPostMonad.SPostPure` | [SP/SPostMonad.v](Code/SP/SPostMonad.v) | proved |
| l.1108-1110: that carrier is the disjunctive, strict sps. | `ASPMonad.monotone_codomain_iff_singleton`, `ASPMonad.join_iff_singleton` | [SP/ASPMonad.v](Code/SP/ASPMonad.v) | proved |
| l.1112-1126, l.1170-1180: disjunctivity, strictness, conjunctivity, termination of base sps. | `RawSP.Disjunctive`, `RawSP.Strict`, `RawSP.Conjunctive`, `RawSP.Terminating` | [SP/RawSP.v](Code/SP/RawSP.v) | proved |
| l.1155-1165: `ASP`, the sps preserving all disjunctions, with (ang) `ret`/`bind`, lawful. | `ASPMonad.ASPSP`, `ASPMonad.retASPSP`, `ASPMonad.bindASPSP`, `ASPMonad.MonadLawsE_ASPSP` | [SP/ASPMonad.v](Code/SP/ASPMonad.v) | proved |
| l.1206-1217: without disjunctivity (conjunctivity) the associativity of the stateful bind fails (Appendix D). | `StatefulSPostCounterexample.FailingBind.SPostStExc_bind_bind_fails`, `StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails`, `StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails` | [SP/StatefulSPostCounterexample.v](Code/SP/StatefulSPostCounterexample.v) | proved |
| l.1218-1220: each class is exactly the transformers of programs under its interpretation (at the arrow level). | `SPostArr.asp_join_iff`, `SPostArr.dslp_meet_iff`, `DSPASLPArr.dsp_hom_iff`, `DSPASLPArr.aslp_hom_iff` | [SP/SPostArr.v](Code/SP/SPostArr.v), [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | proved |
| l.1222-1231: the (ang) `ret` leaves the conjunctive, terminating carrier. | `ASPMonad.dm4all_not_dslp_healthy` | [SP/ASPMonad.v](Code/SP/ASPMonad.v) | partial: shown for [ret] |
| l.1231-1244: `DSLP` with (dem) `ret`/`bind` is lawful. | `DSLPMonad.DSLPSP`, `DSLPMonad.retDSLPSP`, `DSLPMonad.bindDSLPSP`, `DSLPMonad.MonadLawsE_DSLPSP`, `DSLPMonad.meet_iff_msingleton` | [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved |
| l.1257-1347: `DSP` (conjunctive, strict) and `ASLP` (disjunctive, terminating); each element is the meet (join) of its `aspOf` and `dslpOf` parts; both monads are lawful. | `DSPMonad.DSP`, `DSPASLPArr.dspRel`, `DSPASLPArr.aspPartArr`, `DSPASLPArr.dslpPartArr`, `DSPASLPArr.dsp_split`, `DSPMonad.MonadLawsE_DSP`, `ASLPMonad.ASLP`, `DSPASLPArr.aslpRel`, `DSPASLPArr.aspPartAArr`, `DSPASLPArr.dslpPartAArr`, `DSPASLPArr.aslp_split`, `ASLPMonad.MonadLawsE_ASLP` | [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | partial: the parts are defined through the relation an element denotes, not by the displayed formulas |
| l.1343-1345: "its bind is not monotone". |  |  | partial: with state only; see Section 1 above |
| l.1392: the four pure sp monads. | `ASPMonad.MonadLawsE_ASP`, `DSLPMonad.MonadLawsE_DSLP` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved |
| l.1395-1401: the state monad transformer on a lawful monad is lawful. | `Monad.TransformerLaws.MonadLawsE_stateT` | [Lib/Monad/TransformerLaws.v](Code/Lib/Monad/TransformerLaws.v) | partial: generic; [stateT S SPost] itself is not defined |

## Section 3.2, Base sp arrows

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.1419-1478: arrows, application, and the monad of an arrow with application at a fixed input. | `Arrow.Arrow`, `Arrow.ArrowApply`, `ArrowMonad.Monad_Arrow` | [Lib/Arrow/Arrow.v](Code/Lib/Arrow/Arrow.v), [Lib/Arrow/ArrowMonad.v](Code/Lib/Arrow/ArrowMonad.v) | proved |
| l.1496-1502: sp arrows `(B -> P) -> (A -> P)`, monotone. | `SPostArr.SPArrT`, `SPostArr.sp_monotone` | [SP/SPostArr.v](Code/SP/SPostArr.v) | proved |
| l.1506-1539: `ASPArr` (strict + disjunctive = all disjunctions), its operations, lawful; at input `unit` it is `ASP`. | `SPostArr.ASPArr`, `PredicateTransformerProperties.strict_disjunctiveArr_full_join`, `SPostArr.ASP_full_join`, `SPostArr.pureASP`, `SPostArr.compASP`, `SPostArr.firstASP`, `SPostArr.appASP`, `SPostArr.ArrowLaws_ASPArr`, `SPostArr.ArrowApplyLaws_ASPArr`, `ASPMonad.ASP`, `ASPMonad.aspsp_to_asp_morphism`, `ASPMonad.asp_to_aspsp_morphism`, `ASPMonad.aspsp_to_asp_to_aspsp`, `ASPMonad.asp_to_aspsp_to_asp` | [SP/SPostArr.v](Code/SP/SPostArr.v), [SP/PredicateTransformerProperties.v](Code/SP/PredicateTransformerProperties.v), [SP/ASPMonad.v](Code/SP/ASPMonad.v) | proved |
| l.1522-1523: monotonicity and strictness alone are not enough: without disjunctivity the arrow laws fail (Appendix D.3; dually without conjunctivity). | `LawCounterexamples.AngArr.not_ArrowLaws`, `LawCounterexamples.DemArr.not_ArrowLaws` | [SP/LawCounterexamples.v](Code/SP/LawCounterexamples.v) | proved |
| l.1542-1572: `DSLPArr` (terminating + conjunctive = all conjunctions), its operations, lawful; at input `unit` it is `DSLP`. | `SPostArr.DSLPArr`, `PredicateTransformerProperties.terminating_conjunctiveArr_full_meet`, `SPostArr.DSLP_full_meet`, `SPostArr.pureDSLP`, `SPostArr.compDSLP`, `SPostArr.firstDSLP`, `SPostArr.appDSLP`, `SPostArr.ArrowLaws_DSLPArr`, `SPostArr.ArrowApplyLaws_DSLPArr`, `DSLPMonad.DSLP`, `DSLPMonad.dslpsp_to_dslp_morphism`, `DSLPMonad.dslp_to_dslpsp_morphism`, `DSLPMonad.dslpsp_to_dslp_to_dslpsp`, `DSLPMonad.dslp_to_dslpsp_to_dslp` | [SP/SPostArr.v](Code/SP/SPostArr.v), [SP/PredicateTransformerProperties.v](Code/SP/PredicateTransformerProperties.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved |

## Section 3.3, Stateful sp arrows and monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.1586-1597: a lawful arrow with application gives a lawful monad at a fixed input; the state arrow transformer gives the four stateful sp monads. | `ArrowMonad.MonadLawsE_Arrow`, `StateArrowT.Core.stateArrT`, `ASPMonad.ASPSt`, `ASPMonad.MonadLawsE_ASPSt`, `DSLPMonad.DSLPSt`, `DSLPMonad.MonadLawsE_DSLPSt`, `DSPMonad.DSPSt`, `DSPMonad.MonadLawsE_DSPSt`, `ASLPMonad.ASLPSt`, `ASLPMonad.MonadLawsE_ASLPSt` | [Lib/Arrow/ArrowMonad.v](Code/Lib/Arrow/ArrowMonad.v), [Lib/Arrow/StateArrowT/Core.v](Code/Lib/Arrow/StateArrowT/Core.v), [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v), [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved |
| l.1605-1626: the unfolded stateful `ret`/`bind` of ASP and DSLP. | `ASPMonad.getASPSt_ret`, `ASPMonad.getASPSt_bind`, `DSLPMonad.getDSLPSt_ret`, `DSLPMonad.getDSLPSt_bind` | [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | partial: [bind] in relational form, equivalent by disjunctivity resp. conjunctivity |
| l.1632-1648: DSP and ASLP through their parts. | `DSPMonad.getDSPSt_rel`, `DSPMonad.dspRelSt_bind_of`, `ASLPMonad.getASLPSt_rel`, `ASLPMonad.aslpRelSt_bind_of` | [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | partial: relational characterizations |

## Section 3.4, Monads vs. arrows

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.1659-1666: the monad laws are proved once from the arrow laws; the state and exception arrow transformers preserve the laws, so every stateful sp monad is lawful, also with exceptions. | `StateArrowT.Core.ArrowLaws_stateArrT`, `StateArrowT.ArrowApplyLaws.ArrowApplyLaws_stateArrT`, `OptionArrowT.ArrowLaws.ArrowLaws_optionArrT`, `OptionArrowT.ArrowApplyLaws.ArrowApplyLaws_optionArrT`, `ASPMonad.MonadLawsE_ASPStExc`, `DSLPMonad.MonadLawsE_DSLPStExc`, `DSPMonad.MonadLawsE_DSPStExc`, `ASLPMonad.MonadLawsE_ASLPStExc` | [Lib/Arrow/StateArrowT/Core.v](Code/Lib/Arrow/StateArrowT/Core.v), [Lib/Arrow/StateArrowT/ArrowApplyLaws.v](Code/Lib/Arrow/StateArrowT/ArrowApplyLaws.v), [Lib/Arrow/OptionArrowT/ArrowLaws.v](Code/Lib/Arrow/OptionArrowT/ArrowLaws.v), [Lib/Arrow/OptionArrowT/ArrowApplyLaws.v](Code/Lib/Arrow/OptionArrowT/ArrowApplyLaws.v), [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v), [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved |
| l.1667-1669: an arrow morphism gives a monad morphism at a fixed input, and lifts through state and exceptions. | `ArrowMorphism.ArrowMorphism`, `ArrowMorphism.arrow_morphism_monad`, `ArrowMorphism.state_arrow_morphism`, `ArrowMorphism.option_arrow_morphism` | [Lib/Arrow/ArrowMorphism.v](Code/Lib/Arrow/ArrowMorphism.v) | proved |
| l.1676-1708: restricted to monotone, strict, disjunctive transformers, `StT(ASP)` and `StTArr(ASPArr) unit` are isomorphic through `toArrow` and `fromArrow`, with the paper's formulas, as ordered monads. | `ASPMonad.toArrowASPState`, `ASPMonad.fromArrowASPState`, `ASPMonad.toArrowASPState_formula`, `ASPMonad.fromArrowASPState_formula`, `ASPMonad.fromArrowASPState_toArrowASPState`, `ASPMonad.toArrowASPState_fromArrowASPState`, `ASPMonad.toArrowASPState_morphism`, `ASPMonad.fromArrowASPState_morphism` | [SP/ASPMonad.v](Code/SP/ASPMonad.v) | proved |

## Section 3.5, Refined wp monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.1723-1732: the healthiness conditions and the four wp monads AWP, DWLP, DWP, AWLP, lawful. | `WPVariants.wpure_strict`, `WPVariants.wpure_terminating`, `WPVariants.wpure_conjunctive`, `WPVariants.wpure_disjunctive`, `WPVariants.awp_health`, `WPVariants.dwlp_health`, `WPVariants.dwp_health`, `WPVariants.awlp_health`, `WPVariants.AWP`, `WPVariants.DWLP`, `WPVariants.DWP`, `WPVariants.AWLP`, `WPVariants.MonadLawsE_AWP`, `WPVariants.MonadLawsE_DWLP`, `WPVariants.MonadLawsE_DWP`, `WPVariants.MonadLawsE_AWLP` | [WP/WPVariants.v](Code/WP/WPVariants.v) | proved |
| l.1723-1725: the four wp monads contain exactly the wps of programs under their interpretation: each reading lands in its monad, as a monad morphism into it, and every element is the reading of a computation. | `DivNonDet.HealthyReadings.dwpPure_healthy`, `DivNonDet.HealthyReadings.dwlpPure_healthy`, `DivNonDet.HealthyReadings.awpPure_healthy`, `DivNonDet.HealthyReadings.awlpPure_healthy`, `DivNonDet.HealthyReadings.dwpPure_DWP_morphism`, `DivNonDet.HealthyReadings.dwlpPure_DWLP_morphism`, `DivNonDet.HealthyReadings.awpPure_AWP_morphism`, `DivNonDet.HealthyReadings.awlpPure_AWLP_morphism`, `DivNonDet.HealthyReadings.dwpPure_DWP_complete`, `DivNonDet.HealthyReadings.dwlpPure_DWLP_complete`, `DivNonDet.HealthyReadings.awpPure_AWP_complete`, `DivNonDet.HealthyReadings.awlpPure_AWLP_complete` | [Verification/DivNonDet/HealthyReadings.v](Code/Verification/DivNonDet/HealthyReadings.v) | proved |
| l.1734-1738: they share WP's `ret` and `bind`; `ret` has all four properties and `bind` preserves each, so they are submonads of WP. | `WPVariants.toWPure_ret`, `WPVariants.toWPure_bind`, `WPVariants.wpure_ret_strict`, `WPVariants.wpure_ret_terminating`, `WPVariants.wpure_ret_conjunctive`, `WPVariants.wpure_ret_disjunctive`, `WPVariants.wpure_bind_strict`, `WPVariants.wpure_bind_terminating`, `WPVariants.wpure_bind_conjunctive`, `WPVariants.wpure_bind_disjunctive`, `WPVariants.toWPure_morphism` | [WP/WPVariants.v](Code/WP/WPVariants.v) | proved |

## Section 4.1, Taxonomy of triples

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.2747-2763: implication, contrapositive and Galois connection between transformers, and what each says of triples. | `TransformerRelations.pt_le`, `TransformerRelations.pt_le_under`, `TransformerRelations.pt_le_over`, `TransformerRelations.Contrapositive`, `TransformerRelations.Contrapositive_under_over`, `TransformerRelations.Contrapositive_over_under`, `TransformerRelations.GaloisPT`, `TransformerRelations.GaloisPT_over_under` | [PTMonadTaxonomy/TransformerRelations.v](Code/PTMonadTaxonomy/TransformerRelations.v) | proved |
| l.2792-2839: Verscht and Kaminski's diagram (their Figure 5) for the triples of one stateful monadic program: every implication edge is two arrows (under, over), every contrapositive edge two, every Galois edge one. The `Under` triples are named after their logics. Implications, correctness side. | `DivNonDetSt.TriplesTaxonomy.TotalCorr_impl_PartCorr`, `DivNonDetSt.TriplesTaxonomy.TotalCorr_impl_LisbonLogic`, `DivNonDetSt.TriplesTaxonomy.LisbonLogic_impl_AngPartCorr`, `DivNonDetSt.TriplesTaxonomy.PartCorr_impl_AngPartCorr`, `DivNonDetSt.TriplesTaxonomy.dwlp_over_impl_dwp_over`, `DivNonDetSt.TriplesTaxonomy.awlp_over_impl_awp_over`, `DivNonDetSt.TriplesTaxonomy.awp_over_impl_dwp_over`, `DivNonDetSt.TriplesTaxonomy.awlp_over_impl_dwlp_over` | [Verification/DivNonDetSt/TriplesTaxonomy.v](Code/Verification/DivNonDetSt/TriplesTaxonomy.v) | proved |
| Implications, incorrectness side. | `DivNonDetSt.TriplesTaxonomy.aslp_over_impl_asp_over`, `DivNonDetSt.TriplesTaxonomy.aslp_over_impl_dslp_over`, `DivNonDetSt.TriplesTaxonomy.asp_over_impl_dsp_over`, `DivNonDetSt.TriplesTaxonomy.dslp_over_impl_dsp_over`, `DivNonDetSt.TriplesTaxonomy.DemIncorr_impl_PartIncorr`, `DivNonDetSt.TriplesTaxonomy.DemIncorr_impl_IncorrLogic`, `DivNonDetSt.TriplesTaxonomy.PartIncorr_impl_AngPartIncorr`, `DivNonDetSt.TriplesTaxonomy.IncorrLogic_impl_AngPartIncorr` | [Verification/DivNonDetSt/TriplesTaxonomy.v](Code/Verification/DivNonDetSt/TriplesTaxonomy.v) | proved |
| Contrapositives. | `DivNonDetSt.TriplesTaxonomy.LisbonLogic_contra_dwlp_over`, `DivNonDetSt.TriplesTaxonomy.AngPartCorr_contra_dwp_over`, `DivNonDetSt.TriplesTaxonomy.TotalCorr_contra_awlp_over`, `DivNonDetSt.TriplesTaxonomy.PartCorr_contra_awp_over`, `DivNonDetSt.TriplesTaxonomy.DemIncorr_contra_aslp_over`, `DivNonDetSt.TriplesTaxonomy.PartIncorr_contra_asp_over`, `DivNonDetSt.TriplesTaxonomy.IncorrLogic_contra_dslp_over`, `DivNonDetSt.TriplesTaxonomy.AngPartIncorr_contra_dsp_over` | [Verification/DivNonDetSt/TriplesTaxonomy.v](Code/Verification/DivNonDetSt/TriplesTaxonomy.v) | proved |
| Galois connections. | `DivNonDetSt.TriplesTaxonomy.PartCorr_galois_asp_over`, `DivNonDetSt.TriplesTaxonomy.awp_over_galois_PartIncorr` | [Verification/DivNonDetSt/TriplesTaxonomy.v](Code/Verification/DivNonDetSt/TriplesTaxonomy.v) | proved |

## Section 4.2, Monadic relations (Figure 1)

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.2849-2864: DM4all's monadic relation. | `MonadRelation.MonadRelation` | [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v) | proved |
| l.2881-2890: the stateful wp monads are submonads of `WSt`; the order `⊑` on `WSt` is a monadic relation between any two of them. | `WPVariants.toWSt_ret`, `WPVariants.toWSt_bind`, `MonadTaxonomy.impliesWSt`, `MonadTaxonomy.MonadRelation_implies_toWSt`, `MonadTaxonomy.MonadRelation_impliesWSt` | [WP/WPVariants.v](Code/WP/WPVariants.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.2891-2894: what `⊑` between wps says of their triples. | `TransformerRelations.pt_le_under`, `TransformerRelations.pt_le_over` | [PTMonadTaxonomy/TransformerRelations.v](Code/PTMonadTaxonomy/TransformerRelations.v) | partial: the text states both directions reversed; these are the correct ones |
| Figure 1(b), wp implication edges (each also with its converse). | `MonadTaxonomy.MonadRelation_dwp_implies_dwlp`, `MonadTaxonomy.MonadRelation_dwp_implies_awp`, `MonadTaxonomy.MonadRelation_awp_implies_awlp`, `MonadTaxonomy.MonadRelation_dwlp_implies_awlp`, `MonadTaxonomy.MonadRelation_dwlp_implies_dwp`, `MonadTaxonomy.MonadRelation_awp_implies_dwp`, `MonadTaxonomy.MonadRelation_awlp_implies_awp`, `MonadTaxonomy.MonadRelation_awlp_implies_dwlp` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3005-3018: the four stateful sp monads share `SPSt` and its order; `⊑` is not a monadic relation between DSP / ASLP and ASP / DSLP, as their binds are not monotone (Figure 2). | `MonotoneSPSt.SPStMonotone.SPStMon`, `MonadTaxonomy.impliesSPSt`, `DSPMonad.dsp_arbitrary_bind_impossible`, `ASLPMonad.aslp_arbitrary_bind_impossible` | [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | partial: shown for the order on DSP and on ASLP themselves: no left-unital monotone bind exists |
| l.3018-3026, Figure 1(b) sp implication edges: the DSP and ASLP binds are computed through their components, the relations through the components are monadic, and each entails `⊑` of the sps themselves (the asterisks). | `SPStBindComparisons.bindDSPSt_SPStMonotone`, `SPStBindComparisons.bindASLPSt_SPStMonotone`, `MonadTaxonomy.MonadRelation_dsp_implies_asp`, `MonadTaxonomy.MonadRelation_dsp_implies_dslp`, `MonadTaxonomy.MonadRelation_asp_implies_aslp`, `MonadTaxonomy.MonadRelation_dslp_implies_aslp`, `MonadTaxonomy.dsp_implies_asp_part`, `MonadTaxonomy.dsp_implies_dslp_part`, `MonadTaxonomy.asp_implies_aslp_part`, `MonadTaxonomy.dslp_implies_aslp_part` | [PTMonadTaxonomy/SPStBindComparisons.v](Code/PTMonadTaxonomy/SPStBindComparisons.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3036-3057, Figure 1(b) wp contrapositive edges: `⋈` on `WSt` is monadic between AWP and DWLP, DWP and AWLP, one to one, and symmetric. | `MonadTaxonomy.contraWSt`, `MonadTaxonomy.MonadRelation_contraWSt`, `MonadTaxonomy.MonadRelation_contra_awp_dwlp_one`, `MonadTaxonomy.MonadRelation_contra_awp_dwlp_two`, `MonadTaxonomy.MonadRelation_contra_dwp_awlp_one`, `MonadTaxonomy.MonadRelation_contra_dwp_awlp_two`, `MonadTaxonomy.contra_awp_in_dwlp`, `MonadTaxonomy.contra_dwlp_in_awp`, `MonadTaxonomy.contra_dwp_in_awlp`, `MonadTaxonomy.contra_awlp_in_dwp`, `MonadTaxonomy.contraWSt_sym` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3059-3081, Figure 1(b) sp contrapositive edges: `⋈` on `SPSt` is monadic between ASP and DSLP, DSP and ASLP, one to one, swapping the components and meets with joins; symmetric. | `MonadTaxonomy.contraSPSt`, `MonadTaxonomy.MonadRelation_contraSPSt`, `MonadTaxonomy.contraSPSt_meet_join`, `MonadTaxonomy.contraSPSt_join_meet`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_one`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_two`, `MonadTaxonomy.MonadRelation_contra_dsp_aslp_one`, `MonadTaxonomy.MonadRelation_contra_dsp_aslp_two`, `MonadTaxonomy.contra_asp_in_dslp`, `MonadTaxonomy.contra_dslp_in_asp`, `MonadTaxonomy.contra_dsp_in_aslp`, `MonadTaxonomy.contra_aslp_in_dsp`, `MonadTaxonomy.contraSPSt_sym` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3088-3108, Figure 1(b) Galois edge ASP -> DWLP: `Ladj` is a monadic relation (angelic structure), its sps are disjunctive and strict and its wps conjunctive and terminating, it restricts to ASP and DWLP, one to one. | `MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj`, `MonadTaxonomy.GaloisSPWP`, `MonadTaxonomy.Ladj_GaloisSPWP`, `MonadTaxonomy.MonadRelation_GaloisSPWP`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_colim`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_lim`, `MonadTaxonomy.MonadRelation_galois_asp_dwlp`, `MonadTaxonomy.galois_asp_in_dwlp`, `MonadTaxonomy.galois_dwlp_in_asp` | [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3110-3123, Figure 1(b) Galois edge AWP -> DSLP: `Radj`, demonic structure, restricts to AWP and DSLP, one to one. | `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj`, `MonadTaxonomy.GaloisWPSP`, `MonadTaxonomy.Radj_GaloisWPSP`, `MonadTaxonomy.MonadRelation_GaloisWPSP`, `MonadTaxonomy.MonadRelation_galois_awp_dslp`, `MonadTaxonomy.galois_awp_in_dslp`, `MonadTaxonomy.galois_dslp_in_awp` | [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3125-3128: contrapositive pairs exchange `Ladj` and `Radj`. | `MonadTaxonomy.Ladj_iff_Radj` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| Figure 1(a), without state: the wp edges (generic in the two conditions), the sp contrapositive and Galois edges, and the collapse of DSP into ASP and of ASLP into DSLP. | `MonadTaxonomy.MonadRelation_implies_toWPure`, `MonadTaxonomy.MonadRelation_contra_toWPure`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_pure`, `MonadTaxonomy.MonadRelation_contra_dsp_aslp_pure`, `MonadTaxonomy.MonadRelation_galois_asp_dwlp_pure`, `MonadTaxonomy.MonadRelation_galois_awp_dslp_pure`, `MonadTaxonomy.MonadRelation_dsp_asp_pure`, `MonadTaxonomy.MonadRelation_aslp_dslp_pure`, `DSPMonad.dsp_to_asp_morphism`, `DSPMonad.asp_to_dsp_morphism`, `ASLPMonad.aslp_to_dslp_morphism`, `ASLPMonad.dslp_to_aslp_morphism`, `DSPMonad.asp_to_dsp_to_asp`, `DSPMonad.dsp_to_asp_to_dsp`, `ASLPMonad.dslp_to_aslp_to_dslp`, `ASLPMonad.aslp_to_dslp_to_aslp` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved |
| Figure 1(a), the sp implication edges ASLP -> ASP and DSLP -> DSP without state, through the parts as with state; without state every ASP element implies every ASLP element, and every DSP element every DSLP element. | `MonadTaxonomy.MonadRelation_asp_implies_aslp_pure`, `MonadTaxonomy.MonadRelation_dsp_implies_dslp_pure`, `MonadTaxonomy.asp_implies_aslp_any_pure`, `MonadTaxonomy.dsp_implies_dslp_any_pure` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |

## Section 4.4, Effect-modularity

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.3138-3152: each wp relation is proved on `WPure` and lifted by `stateT` (giving exactly the relations on `WSt`) and `optionT`. | `MonadRelation.MonadRelation_stateT`, `MonadRelation.MonadRelation_optionT`, `MonadTaxonomy.MonadRelation_impliesWPure`, `MonadTaxonomy.MonadRelation_contraWPure`, `MonadTaxonomy.impliesWSt_lift`, `MonadTaxonomy.contraWSt_lift`, `MonadTaxonomy.MonadRelation_impliesWStExc`, `MonadTaxonomy.MonadRelation_contraWStExc`, `MonadTaxonomy.MonadRelation_implies_WPSubStExc`, `MonadTaxonomy.MonadRelation_contra_WPSubStExc` | [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3156-3171: the arrow transformers; sp relations are proved once at arbitrary indices, implication as inclusion and contrapositive as equality of the denoted relations, preserved by composition. | `OptionArrowT.Core.optionArrT`, `MonadTaxonomy.dsp_implies_asp_rel`, `MonadTaxonomy.dsp_implies_dslp_rel`, `MonadTaxonomy.asp_implies_aslp_rel`, `MonadTaxonomy.dslp_implies_aslp_rel`, `MonadTaxonomy.contra_asp_dslp_rel`, `MonadTaxonomy.contra_dsp_aslp_rel`, `MonadRelation.MonadRelation_rel_incl`, `MonadRelation.MonadRelation_rel_incl_state`, `MonadRelation.MonadRelation_rel_incl_state_option`, `MonadRelation.MonadRelation_rel_eq`, `MonadRelation.MonadRelation_rel_eq_state`, `MonadRelation.MonadRelation_rel_eq_state_option` | [Lib/Arrow/OptionArrowT/Core.v](Code/Lib/Arrow/OptionArrowT/Core.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v) | proved |
| l.3173-3177: DSP and ASP (ASLP and DSLP) are told apart by a result reachable from two inputs. | `DSPASLPArr.no_ASPArr_for_dsp`, `DSPASLPArr.no_DSLPArr_for_aslp` | [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | proved |
| l.3178-3181: the exception arrow transformer alone keeps DSP = ASP and ASLP = DSLP: the four exception monads, the identity maps as monad morphisms both ways, and all four are specification monads. | `ExceptionCollapse.MonadLawsE_DSPExc`, `ExceptionCollapse.dspExc_to_aspExc_morphism`, `ExceptionCollapse.aspExc_to_dspExc_morphism`, `DSPMonad.asp_to_dsp_to_asp`, `DSPMonad.dsp_to_asp_to_dsp`, `ExceptionCollapse.aslpExc_to_dslpExc_morphism`, `ExceptionCollapse.dslpExc_to_aslpExc_morphism`, `ASLPMonad.dslp_to_aslp_to_dslp`, `ASLPMonad.aslp_to_dslp_to_aslp`, `ExceptionCollapse.OrderedMonad_DSPExc`, `ExceptionCollapse.OrderedMonad_ASLPExc` | [SP/ExceptionCollapse.v](Code/SP/ExceptionCollapse.v), [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | proved |
| l.3183-3187: ASP is `SPost_ang`, DSLP is `SPost_dem`. | `DSLPMonad.dm4all_dem_to_dslp_morphism`, `DSLPMonad.dslp_to_dm4all_dem_morphism`, `DSLPMonad.dm4all_dem_round_trip`, `DSLPMonad.dslp_dm4all_dem_round_trip` | [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | proved |
| l.3188-3191: `SPost_ang` and `SPost_dem` are isomorphic to `Pred` as monads (the angelic maps preserve the order, the demonic ones reverse it). | `PredIsomorphisms.pred_to_dm4all_morphism`, `PredIsomorphisms.dm4all_to_pred_morphism`, `PredIsomorphisms.dm4all_to_pred_to_dm4all`, `PredIsomorphisms.pred_to_dm4all_to_pred`, `PredIsomorphisms.pred_to_dm4all_order`, `PredIsomorphisms.pred_to_dm4all_dem_morphism`, `PredIsomorphisms.dm4all_dem_to_pred_morphism`, `PredIsomorphisms.dm4all_dem_to_pred_to_dm4all_dem`, `PredIsomorphisms.pred_to_dm4all_dem_to_pred`, `PredIsomorphisms.pred_to_dm4all_dem_order` | [SP/PredIsomorphisms.v](Code/SP/PredIsomorphisms.v) | proved |
| l.3192-3195: the adjunctions are proved at the base between `WPure` and `Pred`, and lifted by `stateT` and `optionT`. | `MonadTaxonomy.MonadRelation_GaloisPredWP`, `MonadTaxonomy.MonadRelation_GaloisWPPred`, `MonadTaxonomy.MonadRelation_rel_pred`, `MonadTaxonomy.MonadRelation_rel_pred_state`, `MonadTaxonomy.MonadRelation_rel_pred_state_option`, `MonadTaxonomy.galois_asp_rel`, `MonadTaxonomy.galois_dslp_rel` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |
| l.3197-3200: the diagram again with state and exceptions. | `MonadTaxonomy.MonadRelation_dsp_implies_asp_exc`, `MonadTaxonomy.MonadRelation_dsp_implies_dslp_exc`, `MonadTaxonomy.MonadRelation_asp_implies_aslp_exc`, `MonadTaxonomy.MonadRelation_dslp_implies_aslp_exc`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_exc_one`, `MonadTaxonomy.MonadRelation_contra_asp_dslp_exc_two`, `MonadTaxonomy.MonadRelation_contra_dsp_aslp_exc_one`, `MonadTaxonomy.MonadRelation_contra_dsp_aslp_exc_two`, `MonadTaxonomy.MonadRelation_galois_asp_dwlp_exc`, `MonadTaxonomy.MonadRelation_galois_awp_dslp_exc` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v) | proved |

## Section 5, Specifying monadic programs

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.3247-3293: monad morphisms; triples of a monad morphism, under and over; specification of a computation by an element; specification monads. | `OrderedMonad.MonadMorphism`, `Generic.Triple.triple`, `Generic.Triple.pt_holds`, `Generic.Triple.Under`, `Generic.Triple.Over` | [Lib/Monad/OrderedMonad.v](Code/Lib/Monad/OrderedMonad.v), [Verification/Generic/Triple.v](Code/Verification/Generic/Triple.v) | proved |
| l.3497-3537: the stateful computation monad and the eight stateful morphisms, with their readings on outcomes. | `DivNonDetSt.Computation.stdivndNE`, `DivNonDetSt.Computation.outSt`, `DivNonDetSt.Morphisms.dwpSt_morphism`, `DivNonDetSt.Morphisms.dwlpSt_morphism`, `DivNonDetSt.Morphisms.awpSt_morphism`, `DivNonDetSt.Morphisms.awlpSt_morphism`, `DivNonDetSt.Morphisms.aspSt_morphism`, `DivNonDetSt.Morphisms.dslpSt_morphism`, `DivNonDetSt.Morphisms.dspSt_morphism`, `DivNonDetSt.Morphisms.aslpSt_morphism`, `DivNonDetSt.Triples.dwpSt_read`, `DivNonDetSt.Triples.dwlpSt_read`, `DivNonDetSt.Triples.awpSt_read`, `DivNonDetSt.Triples.awlpSt_read`, `DivNonDetSt.Triples.aspSt_read`, `DivNonDetSt.Triples.dslpSt_read`, `DivNonDetSt.Triples.dspSt_read`, `DivNonDetSt.Triples.aslpSt_read`, `RelSPostArr.dspOf`, `RelSPostArr.aslpOf` | [Verification/DivNonDetSt/Computation.v](Code/Verification/DivNonDetSt/Computation.v), [Verification/DivNonDetSt/Morphisms.v](Code/Verification/DivNonDetSt/Morphisms.v), [Verification/DivNonDetSt/Triples.v](Code/Verification/DivNonDetSt/Triples.v), [Relational/RelSPostArr.v](Code/Relational/RelSPostArr.v) | proved |
| l.3499-3500: the stateful wp morphisms into the refined wp monads. | `DivNonDetSt.HealthyReadings.dwpSt_DWPSt_morphism`, `DivNonDetSt.HealthyReadings.dwlpSt_DWLPSt_morphism`, `DivNonDetSt.HealthyReadings.awpSt_AWPSt_morphism`, `DivNonDetSt.HealthyReadings.awlpSt_AWLPSt_morphism` | [Verification/DivNonDetSt/HealthyReadings.v](Code/Verification/DivNonDetSt/HealthyReadings.v) | proved |
| l.3541-3563: the base wp morphisms, lifted by `stateT` to the stateful ones. | `DivNonDet.Morphisms.dwpPure_morphism`, `DivNonDet.Morphisms.dwlpPure_morphism`, `DivNonDet.Morphisms.awpPure_morphism`, `DivNonDet.Morphisms.awlpPure_morphism`, `Monad.TransformerLaws.MonadMorphism_stateT`, `DivNonDetSt.Morphisms.wpSt_morphism` | [Verification/DivNonDet/Morphisms.v](Code/Verification/DivNonDet/Morphisms.v), [Lib/Monad/TransformerLaws.v](Code/Lib/Monad/TransformerLaws.v), [Verification/DivNonDetSt/Morphisms.v](Code/Verification/DivNonDetSt/Morphisms.v) | proved |
| l.3566-3599: arrow morphisms into the four base sp arrows, lifted through state, and the sp monad morphisms they give. | `SPostArrEquiv.asp_from_rel_morphism`, `SPostArrEquiv.dslp_from_rel_morphism`, `SPostArrEquiv.dsp_from_rel_morphism`, `SPostArrEquiv.aslp_from_rel_morphism`, `DivNonDet.Morphisms.termRel_morphism`, `DivNonDetSt.Morphisms.spSt_morphism`, `DivNonDet.Morphisms.aspPure_morphism_rel`, `DivNonDet.Morphisms.dslpPure_morphism_rel`, `DivNonDet.Morphisms.dspPure_morphism_rel`, `DivNonDet.Morphisms.aslpPure_morphism_rel` | [SP/SPostArrEquiv.v](Code/SP/SPostArrEquiv.v), [Verification/DivNonDet/Morphisms.v](Code/Verification/DivNonDet/Morphisms.v), [Verification/DivNonDetSt/Morphisms.v](Code/Verification/DivNonDetSt/Morphisms.v) | partial: from relations, which the computation reaches through [termRel] |
| l.3614-3653: sp triples; each edge of Figure 1(b) relates the transformers (`_pt`), hence the triples (Section 4.1; examples: ASLP -> ASP, ASP -- DSLP, ASP -> DWLP); incorrectness logic and Lisbon logic. | `MonadTaxonomy.impliesWSt_pt`, `MonadTaxonomy.impliesSPSt_pt`, `MonadTaxonomy.contraWSt_pt`, `MonadTaxonomy.contraSPSt_pt`, `MonadTaxonomy.GaloisSPWP_pt`, `MonadTaxonomy.GaloisWPSP_pt`, `DivNonDetSt.Triples.triple_aspSt`, `DivNonDetSt.Triples.triple_awpSt` | [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [Verification/DivNonDetSt/Triples.v](Code/Verification/DivNonDetSt/Triples.v) | proved |
| l.3657-3705: the running program on even and odd states, its AWP and ASP transformers; Lisbon logic fails (at `s = 1`) where incorrectness logic holds; with `p'` both hold. | `ResetEven.m`, `ResetEven.m_out`, `ResetEven.awp_m`, `ResetEven.asp_m`, `ResetEven.awp_m_q`, `ResetEven.asp_m_p`, `ResetEven.lisbon_p_q_fails`, `ResetEven.incorr_p_q`, `ResetEven.asp_m_p'`, `ResetEven.lisbon_p'_q`, `ResetEven.incorr_p'_q` | [Verification/DivNonDetSt/TriplesExamples/ResetEven.v](Code/Verification/DivNonDetSt/TriplesExamples/ResetEven.v) | proved |
| l.3707-3726: the wp triple sequencing rule, under and over, for any monad morphism into the stateful wp monad, hence for the four readings (all eight kinds). | `DivNonDetSt.TripleRules.wpSt_bind_under`, `DivNonDetSt.TripleRules.wpSt_bind_over` | [Verification/DivNonDetSt/TripleRules.v](Code/Verification/DivNonDetSt/TripleRules.v) | proved |
| l.3728-3735: the ASP and DSLP rules in both directions (Hoare logic and incorrectness logic), and DSP under / ASLP over through their components. | `DivNonDetSt.TripleRules.aspSt_bind_over`, `DivNonDetSt.TripleRules.aspSt_bind_under`, `DivNonDetSt.TripleRules.dslpSt_bind_under`, `DivNonDetSt.TripleRules.dslpSt_bind_over`, `DivNonDetSt.TripleRules.dspSt_under_iff`, `DivNonDetSt.TripleRules.aslpSt_over_iff`, `DivNonDetSt.TripleRules.dspSt_bind_under`, `DivNonDetSt.TripleRules.aslpSt_bind_over`, `DSPSequencing.side_aspSt_under`, `DSPSequencing.inhabited_aspSt_under` | [Verification/DivNonDetSt/TripleRules.v](Code/Verification/DivNonDetSt/TripleRules.v), [Verification/DivNonDetSt/TriplesExamples/DSPSequencing.v](Code/Verification/DivNonDetSt/TriplesExamples/DSPSequencing.v) | partial: the side condition [q0 ⇒ p_a] is right for the over-approximate rules; the under-approximate ones need [p_a ⇒ q0]; under-approximate ASP and over-approximate DSLP, with a family of [p_a], also need an inhabited result type |
| l.3737-3749 (Figure 2): over-approximate DSP and under-approximate ASLP triples do not compose; the counterexample (b) is the complement of (a). | `DSPSequencing.dspSt_over_seq_counterexample`, `DSPSequencing.aslpSt_under_seq_counterexample` | [Verification/DivNonDetSt/TriplesExamples/DSPSequencing.v](Code/Verification/DivNonDetSt/TriplesExamples/DSPSequencing.v) | proved |
| l.3797-3812: the comparison rule is the bind typing of the Dijkstra monad of a morphism; ASP, DSLP and the wp monads are specification monads; DSP and ASLP are not (Section 1). | `DijkstraMonad.DM_bind_typing`, `ASPMonad.OrderedMonad_ASP`, `ASPMonad.OrderedMonad_ASPSt`, `DSLPMonad.OrderedMonad_DSLP`, `DSLPMonad.OrderedMonad_DSLPSt`, `WPVariants.OrderedMonad_DWPSt`, `WPVariants.OrderedMonad_AWPSt`, `WPVariants.OrderedMonad_DWLPSt`, `WPVariants.OrderedMonad_AWLPSt` | [Verification/Generic/DijkstraMonad.v](Code/Verification/Generic/DijkstraMonad.v), [SP/ASPMonad.v](Code/SP/ASPMonad.v), [SP/DSLPMonad.v](Code/SP/DSLPMonad.v), [WP/WPVariants.v](Code/WP/WPVariants.v) | proved |
| l.3817-3839: the AWP specification of the running program, its comparison (a Dijkstra-monad typing), and its equivalence with the pre/post pair. | `ResetEven.wspec`, `ResetEven.awp_m_le_wspec`, `ResetEven.m_DM`, `ResetEven.wspec_pp2wp`, `ResetEven.le_wspec_iff_lisbon` | [Verification/DivNonDetSt/TriplesExamples/ResetEven.v](Code/Verification/DivNonDetSt/TriplesExamples/ResetEven.v) | proved |
| l.3843-3883: wp triples, ASP over and DSLP under triples embed as specifications (`pp2wp_under`, `pp2wp_over`, `pp2asp_over`, `pp2dslp_under`). | `DivNonDetSt.Typings.wpUnderSt`, `DivNonDetSt.Typings.wpOverSt`, `DivNonDetSt.Typings.triple_under_wpSt`, `DivNonDetSt.Typings.triple_over_wpSt`, `Generic.Typings.aspOver`, `Generic.Typings.dslpUnder`, `Generic.Typings.le_aspOver`, `Generic.Typings.le_dslpUnder`, `DivNonDetSt.Typings.triple_over_aspSt`, `DivNonDetSt.Typings.triple_under_dslpSt` | [Verification/DivNonDetSt/Typings.v](Code/Verification/DivNonDetSt/Typings.v), [Verification/Generic/Typings.v](Code/Verification/Generic/Typings.v) | partial: the wp comparisons are in DM4all's order [WP_le], the converse of the paper's l.868-872 order |
| l.3885-3919: no specification embeds ASP under (nor DSLP over) triples; an ASP specification may still match a triple, but typing at it is strictly stronger than the triple. | `DivNonDetSt.Typings.no_asp_under_index`, `DivNonDetSt.Typings.no_dslp_over_index`, `Generic.Typings.le_aspUnder`, `Generic.Typings.aspUnder_typing_triple`, `DijkstraExamples.progA_Dasp_op`, `DijkstraExamples.progloom_harder_not_Dasp_op` | [Verification/DivNonDetSt/Typings.v](Code/Verification/DivNonDetSt/Typings.v), [Verification/Generic/Typings.v](Code/Verification/Generic/Typings.v), [Verification/DivNonDetStExc/DijkstraExamples.v](Code/Verification/DivNonDetStExc/DijkstraExamples.v) | proved |
| l.3944-3974: the Dijkstra monad of a monad morphism, its operations and DM4all's laws; also with the order flipped. | `DijkstraMonad.OrderedTarget`, `DijkstraMonad.DM`, `DijkstraMonad.DM_ret`, `DijkstraMonad.DM_bind`, `DijkstraMonad.DM_wkn`, `DijkstraMonad.DijkstraLaws`, `DijkstraMonad.DM_laws`, `DijkstraMonad.DMop`, `DijkstraMonad.DMop_laws` | [Verification/Generic/DijkstraMonad.v](Code/Verification/Generic/DijkstraMonad.v) | proved |
| l.3974-3993: Dijkstra monads for the four wp monads, ASP and DSLP (with state; with exceptions, with their laws), and the verified examples as their elements. | `DivNonDetSt.DijkstraMonads.OrderedTarget_dwpSt`, `DivNonDetSt.DijkstraMonads.OrderedTarget_dwlpSt`, `DivNonDetSt.DijkstraMonads.OrderedTarget_awpSt`, `DivNonDetSt.DijkstraMonads.OrderedTarget_awlpSt`, `DivNonDetSt.DijkstraMonads.OrderedTarget_aspSt`, `DivNonDetSt.DijkstraMonads.OrderedTarget_dslpSt`, `DivNonDetStExc.DijkstraMonads.Ddwp_laws`, `DivNonDetStExc.DijkstraMonads.Ddwlp_laws`, `DivNonDetStExc.DijkstraMonads.Dawp_laws`, `DivNonDetStExc.DijkstraMonads.Dawlp_laws`, `DivNonDetStExc.DijkstraMonads.Dasp_laws`, `DivNonDetStExc.DijkstraMonads.Ddslp_laws`, `DijkstraExamples.progA_Ddwp`, `DijkstraExamples.progB_Ddwlp`, `DijkstraExamples.progA_Dawp`, `DijkstraExamples.progB_Dawlp`, `DijkstraExamples.progA_Dasp`, `DijkstraExamples.progEx_Ddslp_op` | [Verification/DivNonDetSt/DijkstraMonads.v](Code/Verification/DivNonDetSt/DijkstraMonads.v), [Verification/DivNonDetStExc/DijkstraMonads.v](Code/Verification/DivNonDetStExc/DijkstraMonads.v), [Verification/DivNonDetStExc/DijkstraExamples.v](Code/Verification/DivNonDetStExc/DijkstraExamples.v) | partial: one example per Dijkstra monad |

## Section 6, Galois connections between specification monads

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4099-4120: DM4all's Galois connections between `Pred`, `PrePost` and `WP` (diagram); `Pred` is a specification monad. | `PredMonad.OrderedMonad_Pred`, `BaseGaloisConnections.pred_pp_adjunction`, `BaseGaloisConnections.wp_pp_under_adjunction`, `BaseGaloisConnections.wp_pp_over_adjunction` | [Relational/PredMonad.v](Code/Relational/PredMonad.v), [GaloisConnections/BaseGaloisConnections.v](Code/GaloisConnections/BaseGaloisConnections.v) | proved |
| l.4109-4120, the `SPost` -- `Pred` edge of the diagram. | `GaloisArr.Galois_Rel_SPost` | [GaloisConnections/GaloisArr.v](Code/GaloisConnections/GaloisArr.v) | partial: for binary arrows, monotone sps and relations, at input [unit] |
| l.4124-4126: in the pure case `SPost ~ Pred` (Section 4.4 above). | `PredIsomorphisms.pred_to_dm4all_morphism` | [SP/PredIsomorphisms.v](Code/SP/PredIsomorphisms.v) | proved |
| l.4130-4134: monotone monad transformers preserve Galois connections. | `MonadRelation.MonadRelation_stateT`, `MonadRelation.MonadRelation_optionT` | [Lib/Monad/MonadRelation.v](Code/Lib/Monad/MonadRelation.v) | partial: they preserve monadic relations, which the Galois connections are in Section 4 |
| l.4262-4316: the stateful `Pred`; `φ` and `ψ` are monad morphisms (angelic structure); `Ladj (φ p) (ψ p)`, and every `Ladj` pair is of this form; `φ ⊣ φ'` and `φ'` preserves the angelic structure (the paper says demonic); the adjoints are colimit/limit preserving; ASP is isomorphic to DWLP. | `PredMonad.PredSt.PredSt`, `PredMonad.PredSt.ordPredSt`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_ret`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_bind`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_ret`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_bind`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_fromPred`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_pred`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_toPred_adj`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_ret`, `MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_bind`, `MonadTaxonomy.galois_asp_dwlp_order`, `SPostArrEquiv.asp_to_rel_morphism` | [Relational/PredMonad.v](Code/Relational/PredMonad.v), [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [SP/SPostArrEquiv.v](Code/SP/SPostArrEquiv.v) | proved |
| l.4325-4379: the demonic side: `ξ` (monotone into `Pred^op`), `ζ`, `ξ'`; `ξ' ⊣ ξ`; `ξ` and `ζ` are monad morphisms (demonic structure); the lax demonic bind (footnote); `Radj (ξ p) (ζ p)`, and every `Radj` pair is of this form; nuclei and limits; DSLP is isomorphic to AWP. | `MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_antitone`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.toPred`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_toPred_adj`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_ret`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_bind`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_ret`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_bind`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.bindP`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.lunit`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.runit`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.assoc`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_fromPred`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_pred`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_toPred`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.tPfP_unit`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.tPfP_unit_inv`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_unit`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_unit_inv`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_lim`, `MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_colim`, `MonadTaxonomy.galois_awp_dslp_order`, `SPostArrEquiv.dslp_to_rel_morphism` | [PTMonadTaxonomy/MonotoneSPSt.v](Code/PTMonadTaxonomy/MonotoneSPSt.v), [PTMonadTaxonomy/MonadTaxonomy.v](Code/PTMonadTaxonomy/MonadTaxonomy.v), [SP/SPostArrEquiv.v](Code/SP/SPostArrEquiv.v) | proved |

## Section 7, Formalization in Rocq

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4428-4430: example programs that together use all sixteen kinds of triples (index: `Verification/DivNonDetStExc/TriplesExamples.v`). | `ProgA.progA_dwp_under`, `ProgRet.progRet_dwp_over`, `ProgB.progB_dwlp_under`, `ProgRet.progRet_dwlp_over`, `ProgA.progA_awp_under`, `ProgA.progA_awp_over`, `ProgB.progB_awlp_under`, `ProgRet.progRet_awlp_over`, `ProgA.progA_asp_under`, `ProgA.progA_asp_over`, `ProgEx.progEx_dslp_under`, `ProgA.progA_dslp_over`, `ProgRet.progRet_dsp_under`, `ProgRet.progRet_dsp_over`, `ProgRet.progRet_aslp_under`, `ProgRet.progRet_aslp_over` | [Verification/DivNonDetStExc/TriplesExamples/ProgA.v](Code/Verification/DivNonDetStExc/TriplesExamples/ProgA.v), [Verification/DivNonDetStExc/TriplesExamples/ProgRet.v](Code/Verification/DivNonDetStExc/TriplesExamples/ProgRet.v), [Verification/DivNonDetStExc/TriplesExamples/ProgB.v](Code/Verification/DivNonDetStExc/TriplesExamples/ProgB.v), [Verification/DivNonDetStExc/TriplesExamples/ProgEx.v](Code/Verification/DivNonDetStExc/TriplesExamples/ProgEx.v) | proved |
| l.4431-4432: programs written as interaction trees, mapped into the computation monad by a monad morphism. | `DivNonDet.Computation.denote_morphism`, `DivNonDetSt.Computation.denoteSt_morphism`, `DivNonDetStExc.Computation.denoteStExc_morphism` | [Verification/DivNonDet/Computation.v](Code/Verification/DivNonDet/Computation.v), [Verification/DivNonDetSt/Computation.v](Code/Verification/DivNonDetSt/Computation.v), [Verification/DivNonDetStExc/Computation.v](Code/Verification/DivNonDetStExc/Computation.v) | proved |
| l.4437-4442: all sp arrows are choice arrows, with Hughes's laws and Paterson's distribution law; the transformers preserve them. | `Arrow.ArrowChoiceLaws`, `SPostArr.ArrowChoiceLaws_ASPArr`, `SPostArr.ArrowChoiceLaws_DSLPArr`, `DSPASLPArr.ArrowChoiceLaws_DSPArr`, `DSPASLPArr.ArrowChoiceLaws_ASLPArr`, `StateArrowT.ArrowChoiceLaws.ArrowChoiceLaws_stateArrT`, `OptionArrowT.ArrowChoiceLaws.ArrowChoiceLaws_optionArrT` | [Lib/Arrow/Arrow.v](Code/Lib/Arrow/Arrow.v), [SP/SPostArr.v](Code/SP/SPostArr.v), [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v), [Lib/Arrow/StateArrowT/ArrowChoiceLaws.v](Code/Lib/Arrow/StateArrowT/ArrowChoiceLaws.v), [Lib/Arrow/OptionArrowT/ArrowChoiceLaws.v](Code/Lib/Arrow/OptionArrowT/ArrowChoiceLaws.v) | partial: the sentence also says loop arrows, which they are not: no sp arrow has an [ArrowLoop] instance |
| l.4412-4413, "about 28k lines", "only funext, propext and excluded middle" (the build has about 38.6k lines; `Checks/Assumptions.v` reports the axioms, which also include `eq_rect_eq`, through ITree). |  |  | not checkable |

## Appendix A, Arrow laws

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4537-4557: the twelve laws, with logical equivalence of sp arrows as the equality. | `Arrow.ArrowLaws`, `Arrow.ArrowApplyLaws`, `SPostArr.ASPArr_eq`, `SPostArr.DSLPArr_eq`, `DSPASLPArr.DSPArr_eq`, `DSPASLPArr.ASLPArr_eq` | [Lib/Arrow/Arrow.v](Code/Lib/Arrow/Arrow.v), [SP/SPostArr.v](Code/SP/SPostArr.v), [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | proved |

## Appendix B, The DSP and ASLP arrows

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4561-4645: the two arrows, their parts, operations and laws; direct composition of dsps fails; at input `unit` they give DSP and ASLP. | `DSPASLPArr.DSPArr`, `DSPASLPArr.pure_DSP`, `DSPASLPArr.comp_DSP`, `DSPASLPArr.first_DSP`, `DSPASLPArr.app_DSP`, `DSPASLPArr.ArrowLaws_DSPArr`, `DSPASLPArr.ArrowApplyLaws_DSPArr`, `SPostArrInfrastructure.dsp_naive_transformer_comp_rejects`, `DSPASLPArr.ASLPArr`, `DSPASLPArr.pure_ASLP`, `DSPASLPArr.comp_ASLP`, `DSPASLPArr.first_ASLP`, `DSPASLPArr.app_ASLP`, `DSPASLPArr.ArrowLaws_ASLPArr`, `DSPASLPArr.ArrowApplyLaws_ASLPArr`, `DSPMonad.dspsp_to_dsp_morphism`, `DSPMonad.dsp_to_dspsp_morphism`, `ASLPMonad.aslpsp_to_aslp_morphism`, `ASLPMonad.aslp_to_aslpsp_morphism`, `DSPMonad.dspsp_to_dsp_to_dspsp`, `DSPMonad.dsp_to_dspsp_to_dsp`, `ASLPMonad.aslpsp_to_aslp_to_aslpsp`, `ASLPMonad.aslp_to_aslpsp_to_aslp` | [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v), [Tests/SPostArrInfrastructure.v](Code/Tests/SPostArrInfrastructure.v), [SP/DSPMonad.v](Code/SP/DSPMonad.v), [SP/ASLPMonad.v](Code/SP/ASLPMonad.v) | partial: on non-pure arrows; the parts are defined through the relation an element denotes, not by the displayed formulas |

## Appendix C, Fixing the input of the ASP and DSLP arrows

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4647-4732: Lemma lem:asp-singleton; fixing the input of `ASPArr` gives the carrier and the `ret` and `bind` of `ASP`. | `ASPMonad.getASP_singleton`, `ASPMonad.join_iff_singleton`, `ASPMonad.getASP_ret`, `ASPMonad.getASP_bind`, `ASPMonad.aspsp_to_asp_morphism` | [SP/ASPMonad.v](Code/SP/ASPMonad.v) | partial: [bind] read in relational form; the carrier equivalence is proved classically, not constructively |
| l.4733-4786: dually Lemma lem:dslp-singleton, and the `ret` and `bind` of `DSLP`. | `DSLPMonad.getDSLP_msingleton`, `DSLPMonad.meet_iff_msingleton`, `DSLPMonad.getDSLP_ret`, `DSLPMonad.getDSLP_bind`, `DSLPMonad.dslpsp_to_dslp_morphism` | [SP/DSLPMonad.v](Code/SP/DSLPMonad.v) | partial: [bind] read in relational form |

## Appendix D, Counterexamples to the monad and arrow laws

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4810-4854, D.1: `SPost_ang(S, A)` (monotone, strict) with the (ang-st) operations: the unit laws hold, associativity fails, with the paper's `m`, `f`, `g` (at `S = A = bool`). | `StatefulSPostCounterexample.St.SPostSt`, `StatefulSPostCounterexample.St.SPostSt_bind_ret_r`, `StatefulSPostCounterexample.St.SPostSt_bind_ret_l`, `StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails` | [SP/StatefulSPostCounterexample.v](Code/SP/StatefulSPostCounterexample.v) | proved |
| l.4856-4886, D.2: `SPost_dem(S, A)` (monotone, terminating) with the (dem-st) operations: the unit laws hold, associativity fails, with the paper's `m`, `f`, `g` (at `S = A = bool`). | `StatefulSPostCounterexample.Dem.SPostDem`, `StatefulSPostCounterexample.Dem.SPostDem_bind_ret_r`, `StatefulSPostCounterexample.Dem.SPostDem_bind_ret_l`, `StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails` | [SP/StatefulSPostCounterexample.v](Code/SP/StatefulSPostCounterexample.v) | proved |
| l.4888-4927, D.3: the monotone, strict sp arrows with the operations of `ASPArr` (the codomain condition amounts to strictness) fail `first f >>> arr fst = arr fst >>> f`, with the paper's `g` and `pre`; dually for the monotone, terminating arrows with those of `DSLPArr`. | `LawCounterexamples.AngArr.SPArrAng`, `LawCounterexamples.AngArr.codomain_iff_strict`, `LawCounterexamples.AngArr.compAng_ASP`, `LawCounterexamples.AngArr.first_fst_fails`, `LawCounterexamples.AngArr.not_ArrowLaws`, `LawCounterexamples.DemArr.SPArrDem`, `LawCounterexamples.DemArr.codomain_iff_terminating`, `LawCounterexamples.DemArr.compDem_DSLP`, `LawCounterexamples.DemArr.first_fst_fails`, `LawCounterexamples.DemArr.not_ArrowLaws` | [SP/LawCounterexamples.v](Code/SP/LawCounterexamples.v) | proved |

## Appendix E, Decomposing dsp and aslp transformers

| Paper | Rocq name(s) | File | Status |
|---|---|---|---|
| l.4929-5086: Lemmas lem:dsp-split and lem:aslp-split, and the health of the components. | `DSPASLPArr.dsp_split`, `DSPASLPArr.aspPartArr`, `DSPASLPArr.dslpPartArr`, `DSPASLPArr.aslp_split`, `DSPASLPArr.aspPartAArr`, `DSPASLPArr.dslpPartAArr` | [SP/DSPASLPArr.v](Code/SP/DSPASLPArr.v) | partial: the components are defined through the relation an element denotes, not by the displayed formulas; their health holds by their types |

## Gaps and differences from the paper

The rows marked *partial* above say where the formalization differs from
a claim. The following are places where the
paper's text and the formalization disagree; the Rocq statements are the
reference.

- **l.668-670 and l.1343-1345.** The DSP and ASLP `bind`s are not monotone
  only with state (`DSPMonad.not_OrderedMonad_DSPSt`,
  `ASLPMonad.not_OrderedMonad_ASLPSt`). Without state DSP and ASLP are
  ASP and DSLP, hence specification monads (`DSPMonad.OrderedMonad_DSP`,
  `ASLPMonad.OrderedMonad_ASLP`).
- **l.672-679.** The introduction swaps *asp* and *dslp*: the triples that
  embed in Dijkstra monads are ASP over and DSLP under
  (`DivNonDetSt.Typings.triple_over_aspSt`,
  `DivNonDetSt.Typings.triple_under_dslpSt`); ASP under and DSLP over have
  no index (`DivNonDetSt.Typings.no_asp_under_index`,
  `DivNonDetSt.Typings.no_dslp_over_index`). Section 5 (l.3866-3888) agrees
  with the code.
- **l.2891-2894.** The direction of the implication between triples is
  reversed: `wp1 ⊑ wp2` gives under-approximate triples of `wp1` to `wp2`
  and over-approximate ones of `wp2` to `wp1`
  (`TransformerRelations.pt_le_under`, `TransformerRelations.pt_le_over`).
- **l.3048-3050, l.3075-3077.** The labels are swapped: "over-approximate
  triple of wp1 / sp1" should read under-approximate, and "under-approximate
  triple of wp2 / sp2" over-approximate (by the terminology of l.2786).
- **l.3088-3119.** `Ladj` is used as `Ladj sp wp` but typed `WSt -> SPSt ->
  P`; in it the sp is the left adjoint (the text says right), and in `Radj`
  the wp is (the text says sps are left adjoint).
- **l.3152.** The type of `WStExc` is missing its final `-> P`.
- **Figure 1(b).** The two ASLP implication edges also go through a
  component (`MonadTaxonomy.asp_implies_aslp_part`,
  `MonadTaxonomy.dslp_implies_aslp_part`), as the text says, but carry no
  asterisk.
- **l.4303.** `φ'` preserves the angelic structure
  (`MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_ret`, `toPred_bind`);
  the text says demonic.
- **l.4331.** `ξ` quantifies `∀ s0` (as the calculation at l.4360 uses), not
  `∃ s0`.
- **l.3849-3861.** The `pp2wp` comparisons hold in DM4all's order on wps
  (`WPure.WP_le`), the converse of the paper's pointwise order (l.868-872).
- **l.4133.** Monad transformers are shown to preserve monadic relations
  (`MonadRelation.MonadRelation_stateT`, `MonadRelation.MonadRelation_optionT`),
  which is how Section 4 states the Galois connections; preservation of
  Galois connections as such is not stated.
- **Section 7, l.4412.** The build has about 38.6k lines of Rocq (the files of
  `_CoqProject`), not 28k. Besides functional and propositional
  extensionality and excluded middle, the interaction-tree layer uses
  `eq_rect_eq` (through ITree and paco); `Checks/Assumptions.v` reports
  them.
- **Section 7, l.4437.** The sp arrows are not loop arrows: none has an
  `ArrowLoop` instance, and for the option-stacked arrows none can be
  lawful (`OptionLoop.optionRel_no_lawful_ArrowLoop`,
  `SPostArrEquiv.optionASP_no_lawful_ArrowLoop`,
  `SPostArrEquiv.optionDSLP_no_lawful_ArrowLoop`).
- **l.3728-3735, sequencing of sp triples.** The rules are not simply
  "analogous" to the wp one. The side condition `q0(a,s) ⇒ p_a(s)` is right
  for the over-approximate rules (Hoare logic, over-approximate DSLP and
  ASLP); the under-approximate ones (incorrectness logic, under-approximate
  DSLP and DSP) need `p_a(s) ⇒ q0(a,s)`. Under-approximate ASP and
  over-approximate DSLP, with a family `p_a`, also need an inhabited result
  type. `DSPSequencing.side_aspSt_under`,
  `DSPSequencing.inhabited_aspSt_under` show that both hypotheses are
  needed.
- **l.510-515, l.529-533, l.1395-1401 and l.1676-1708.** The paper motivates
  the arrows by the state monad transformer on `ASP` not giving the
  expected monad, but restricted to healthy elements the two constructions
  are isomorphic as ordered monads (`ASPMonad.toArrowASPState_morphism`,
  `ASPMonad.fromArrowASPState_morphism`), which
  l.1676-1708 itself states. The motivation may want rewording.
- **Section 4.3** has no code.

## Old paths in the paper's source

These paths appear only in comments and unrendered draft notes of the
paper's source.

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
| `Taxonomy/BaseSpecMonads/NewGaloisConnections.v` | does not exist; its content is `BaseGaloisConnections.wp_pp_over_adjunction` (Section 6) |
