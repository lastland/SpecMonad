(** * Paper claims index

    One block per section of the paper, in paper order.  Each block quotes
    or paraphrases a claim, with its line in the paper's source, and
    [Check]s the Rocq names that state it.  Where the formalization differs
    from the claim the comment says how ("partial: ...").  This file holds only what the paper claims.  [PAPER.md] at the
    repository root is the evaluator-facing table built from this file.
    Assumptions are reported by [Checks/Assumptions.v].

    Modules are required without [Import] and names are qualified by file
    (by directory too where several files share a name, and by [Module]
    where the file has one), so a [Check] fails if a name moves. *)

From Incorrectness.Lib.Monad Require
  OrderedMonad MonadRelation TransformerLaws.
From Incorrectness.Lib.Arrow Require
  Arrow ArrowMonad ArrowMorphism.
From Incorrectness.Lib.Arrow.StateArrowT Require
  Core ArrowApplyLaws ArrowChoiceLaws.
From Incorrectness.Lib.Arrow.OptionArrowT Require
  Core ArrowLaws ArrowApplyLaws ArrowChoiceLaws.
From Incorrectness.Relational Require
  PredMonad RelSPostArr.
From Incorrectness.WP Require
  WPure WPVariants.
From Incorrectness.SP Require
  RawSP SPostMonad StatefulSPostCounterexample PredicateTransformerProperties
  SPostArr DSPASLPArr SPostArrEquiv ASPMonad DSLPMonad DSPMonad ASLPMonad
  ExceptionCollapse PredIsomorphisms LawCounterexamples.
From Incorrectness.PTMonadTaxonomy Require
  TransformerRelations MonotoneSPSt SPStBindComparisons MonadTaxonomy.
From Incorrectness.Verification.Generic Require
  Triple DijkstraMonad Typings.
From Incorrectness.Verification.DivNonDet Require
  Computation Morphisms Triples TriplesTaxonomy HealthyReadings.
From Incorrectness.Verification.DivNonDetSt Require
  Computation Morphisms Triples TriplesTaxonomy Typings DijkstraMonads
  HealthyReadings TripleRules.
From Incorrectness.Verification.DivNonDetSt.TriplesExamples Require
  ResetEven DSPSequencing.
From Incorrectness.Verification.DivNonDetStExc Require
  Computation Morphisms DijkstraMonads TriplesExamples DijkstraExamples.
From Incorrectness.GaloisConnections Require
  BaseGaloisConnections GaloisArr.
From Incorrectness.Tests Require
  SPostArrInfrastructure.

(* ================================================================= *)
(** ** Section 1, Introduction                                       *)
(* ================================================================= *)

(** Claims of the introduction that later sections do not restate.  The
    contribution bullets are backed in the sections they point to. *)

(** l.427-439: partial correctness is [p => dwlp c q], equivalently
    [asp c p => q]; incorrectness logic is [q => asp c p] (for monadic
    stateful programs; [PartCorr], [IncorrLogic] are the named triples). *)
Check DivNonDetSt.TriplesTaxonomy.PartCorr_galois_asp_over.
Check DivNonDetSt.Triples.triple_aspSt.

(** l.469-473: the state transformer on the wp monad. *)
Check WPure.WSt.
Check WPure.MonadLawsE__WSt.

(** l.479: "monotone sps alone do not form a lawful monad" (partial: for
    the angelic structure on monotone stateful transformers, left unit holds
    only as an inequation; the converse fails for an inhabited state). *)
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.lunitStrictlyLax.

(** l.483: Maillard et al.'s [SPost] specifies programs under the angelic,
    total interpretation: it is isomorphic to [ASP] as a monad. *)
Check ASPMonad.dm4all_to_asp_morphism.
Check ASPMonad.asp_to_dm4all_morphism.
Check ASPMonad.dm4all_round_trip.
Check ASPMonad.asp_dm4all_round_trip.

(** l.490-496: the four homomorphism properties of sps. *)
Check PredicateTransformerProperties.StrictArr.
Check PredicateTransformerProperties.TerminatingArr.
Check PredicateTransformerProperties.ConjunctiveArr.
Check PredicateTransformerProperties.DisjunctiveArr.

(** l.568-573: a specification monad is a monad ordered so that [bind] is
    monotone. *)
Check OrderedMonad.OrderedMonad.

(** l.639-641: the base computation monad of nondeterminism and
    nontermination. *)
Check DivNonDet.Computation.divndNE.

(** l.643-644: state and exceptions on both sides; the morphisms lift for
    free. *)
Check Monad.TransformerLaws.MonadMorphism_optionT.
Check ArrowMorphism.state_option_arrow_morphism.
Check DivNonDetStExc.Morphisms.dwpStExc_morphism.
Check DivNonDetStExc.Morphisms.aspStExc_morphism_rel.
Check DivNonDetStExc.Morphisms.dspStExc_morphism_rel.

(** l.650-653: simple programs proved to satisfy correctness and
    incorrectness triples, and O'Hearn's example (all sixteen kinds: Section
    7). *)
Check ProgA.progA_dwp_under.
Check ProgA.progA_asp_under.
Check ProgEx.progEx_dslp_under.
Check OHearn.example_incorrect.

(** l.655-656: asp, dslp and all wp monads are specification monads, also
    with exceptions; l.662: flipping the order covers over- and
    under-approximation. *)
Check ASPMonad.OrderedMonad_ASPStExc.
Check DSLPMonad.OrderedMonad_DSLPStExc.
Check WPure.OrderedMonad_WStExc.
Check OrderedMonad.OrderedMonad_flip.

(** l.668-670: the dsp and aslp binds are not monotone (partial: with
    state only; without state DSP and ASLP coincide with ASP and DSLP, see
    Section 4.2).  l.672-679: which triples embed in Dijkstra monads (the
    bullet swaps asp and dslp; the artifact and Section 5 agree that asp
    over and dslp under embed, asp under and dslp over do not); backed in
    Section 5. *)
Check DSPMonad.not_OrderedMonad_DSPSt.
Check ASLPMonad.not_OrderedMonad_ASLPSt.

(** l.738-742: Galois connections with stateful [Pred] (Section 6) and
    pre/post specifications (partial: as Galois connections of binary
    arrows, at input [S]). *)
Check GaloisArr.Galois_Rel_PrePost.
Check GaloisArr.Galois_WP_PrePost.

(** l.740-748: the isomorphism between [Pred] and [SPost] extends to
    isomorphisms between asp and dwlp and between dslp and awp as stateful
    specification monads (partial: order isomorphisms, compatible with the
    monad structure, through the Galois relations; see Section 6). *)
Check MonadTaxonomy.galois_asp_dwlp_order.
Check MonadTaxonomy.galois_awp_dslp_order.
Check PredIsomorphisms.pred_to_dm4all_morphism.

(* ================================================================= *)
(** ** Section 2, Background: weakest precondition monads            *)
(* ================================================================= *)

(** l.799-813: the monotone continuation monad on [P], with its [ret] and
    [bind]; l.840-866: monotonicity, preserved by [ret] and [bind]. *)
Check WPure.WPure.
Check WPure.wpure_mono.
Check WPure.retWPure.
Check WPure.bindWPure.
Check WPure.MonadLawsE_WPure.
Check WPVariants.wpure_ret_mono.
Check WPVariants.wpure_bind_mono.

(** l.868-876: the pointwise order, preserved by [ret] and [bind]
    ([WP_le] is DM4all's direction, the converse of the paper's). *)
Check WPure.WP_le.
Check WPure.OrderedMonad_WPure.

(** l.886-913: the stateful wp monad, ordered, with monotone [bind]. *)
Check WPure.retPs.
Check WPure.bindPs.
Check WPure.ordWSt.
Check WPure.OrderedMonad_WSt.

(* ================================================================= *)
(** ** Section 3.1, Base sp monads                                   *)
(* ================================================================= *)

(** l.1080-1082: an sp of a pure program, [P -> (A -> P)]. *)
Check RawSP.SPPure.

(** l.1088-1108: Maillard et al.'s [SPost] (monotone, postconditions imply
    the precondition), with (ang) [ret]/[bind], is lawful. *)
Check SPostMonad.SPM.SPost.
Check SPostMonad.SPM.retSP.
Check SPostMonad.SPM.bindSP.
Check SPostMonad.SPMFacts.MonadLawsE_SPost.
Check SPostMonad.SPostPure.

(** l.1108-1110: that carrier is the disjunctive, strict sps. *)
Check ASPMonad.monotone_codomain_iff_singleton.
Check ASPMonad.join_iff_singleton.

(** l.1112-1126, l.1170-1180: disjunctivity, strictness, conjunctivity,
    termination of base sps. *)
Check RawSP.Disjunctive.
Check RawSP.Strict.
Check RawSP.Conjunctive.
Check RawSP.Terminating.

(** l.1155-1165: [ASP], the sps preserving all disjunctions, with (ang)
    [ret]/[bind], lawful. *)
Check ASPMonad.ASPSP.
Check ASPMonad.retASPSP.
Check ASPMonad.bindASPSP.
Check ASPMonad.MonadLawsE_ASPSP.

(** l.1206-1217: without disjunctivity (conjunctivity) the associativity
    of the stateful bind fails (Appendix D). *)
Check StatefulSPostCounterexample.FailingBind.SPostStExc_bind_bind_fails.
Check StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails.
Check StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails.

(** l.1218-1220: each class is exactly the transformers of programs under
    its interpretation (at the arrow level). *)
Check SPostArr.asp_join_iff.
Check SPostArr.dslp_meet_iff.
Check DSPASLPArr.dsp_hom_iff.
Check DSPASLPArr.aslp_hom_iff.

(** l.1222-1231: the (ang) [ret] leaves the conjunctive, terminating
    carrier (partial: shown for [ret]). *)
Check ASPMonad.dm4all_not_dslp_healthy.

(** l.1231-1244: [DSLP] with (dem) [ret]/[bind] is lawful. *)
Check DSLPMonad.DSLPSP.
Check DSLPMonad.retDSLPSP.
Check DSLPMonad.bindDSLPSP.
Check DSLPMonad.MonadLawsE_DSLPSP.
Check DSLPMonad.meet_iff_msingleton.

(** l.1257-1347: [DSP] (conjunctive, strict) and [ASLP] (disjunctive,
    terminating); each element is the meet (join) of its [aspOf] and
    [dslpOf] parts; both monads are lawful (partial: the parts are defined
    through the relation an element denotes, not by the displayed
    formulas). *)
Check DSPMonad.DSP.
Check DSPASLPArr.dspRel.
Check DSPASLPArr.aspPartArr.
Check DSPASLPArr.dslpPartArr.
Check DSPASLPArr.dsp_split.
Check DSPMonad.MonadLawsE_DSP.
Check ASLPMonad.ASLP.
Check DSPASLPArr.aslpRel.
Check DSPASLPArr.aspPartAArr.
Check DSPASLPArr.dslpPartAArr.
Check DSPASLPArr.aslp_split.
Check ASLPMonad.MonadLawsE_ASLP.

(** l.1343-1345: "its bind is not monotone" (partial: with state only; see
    Section 1 above). *)

(** l.1392: the four pure sp monads. *)
Check ASPMonad.MonadLawsE_ASP.
Check DSLPMonad.MonadLawsE_DSLP.

(** l.1395-1401: the state monad transformer on a lawful monad is lawful
    (partial: generic; [stateT S SPost] itself is not defined). *)
Check Monad.TransformerLaws.MonadLawsE_stateT.

(* ================================================================= *)
(** ** Section 3.2, Base sp arrows                                   *)
(* ================================================================= *)

(** l.1419-1478: arrows, application, and the monad of an arrow with
    application at a fixed input. *)
Check Arrow.Arrow.
Check Arrow.ArrowApply.
Check ArrowMonad.Monad_Arrow.

(** l.1496-1502: sp arrows [(B -> P) -> (A -> P)], monotone. *)
Check SPostArr.SPArrT.
Check SPostArr.sp_monotone.

(** l.1506-1539: [ASPArr] (strict + disjunctive = all disjunctions), its
    operations, lawful; at input [unit] it is [ASP]. *)
Check SPostArr.ASPArr.
Check PredicateTransformerProperties.strict_disjunctiveArr_full_join.
Check SPostArr.ASP_full_join.
Check SPostArr.pureASP.
Check SPostArr.compASP.
Check SPostArr.firstASP.
Check SPostArr.appASP.
Check SPostArr.ArrowLaws_ASPArr.
Check SPostArr.ArrowApplyLaws_ASPArr.
Check ASPMonad.ASP.
Check ASPMonad.aspsp_to_asp_morphism.
Check ASPMonad.asp_to_aspsp_morphism.
Check ASPMonad.aspsp_to_asp_to_aspsp.
Check ASPMonad.asp_to_aspsp_to_asp.

(** l.1522-1523: monotonicity and strictness alone are not enough: without
    disjunctivity the arrow laws fail (Appendix D.3; dually without
    conjunctivity). *)
Check LawCounterexamples.AngArr.not_ArrowLaws.
Check LawCounterexamples.DemArr.not_ArrowLaws.

(** l.1542-1572: [DSLPArr] (terminating + conjunctive = all conjunctions),
    its operations, lawful; at input [unit] it is [DSLP]. *)
Check SPostArr.DSLPArr.
Check PredicateTransformerProperties.terminating_conjunctiveArr_full_meet.
Check SPostArr.DSLP_full_meet.
Check SPostArr.pureDSLP.
Check SPostArr.compDSLP.
Check SPostArr.firstDSLP.
Check SPostArr.appDSLP.
Check SPostArr.ArrowLaws_DSLPArr.
Check SPostArr.ArrowApplyLaws_DSLPArr.
Check DSLPMonad.DSLP.
Check DSLPMonad.dslpsp_to_dslp_morphism.
Check DSLPMonad.dslp_to_dslpsp_morphism.
Check DSLPMonad.dslpsp_to_dslp_to_dslpsp.
Check DSLPMonad.dslp_to_dslpsp_to_dslp.

(* ================================================================= *)
(** ** Section 3.3, Stateful sp arrows and monads                    *)
(* ================================================================= *)

(** l.1586-1597: a lawful arrow with application gives a lawful monad at a
    fixed input; the state arrow transformer gives the four stateful sp
    monads. *)
Check ArrowMonad.MonadLawsE_Arrow.
Check StateArrowT.Core.stateArrT.
Check ASPMonad.ASPSt.
Check ASPMonad.MonadLawsE_ASPSt.
Check DSLPMonad.DSLPSt.
Check DSLPMonad.MonadLawsE_DSLPSt.
Check DSPMonad.DSPSt.
Check DSPMonad.MonadLawsE_DSPSt.
Check ASLPMonad.ASLPSt.
Check ASLPMonad.MonadLawsE_ASLPSt.

(** l.1605-1626: the unfolded stateful [ret]/[bind] of ASP and DSLP
    (partial: [bind] in relational form, equivalent by disjunctivity
    resp. conjunctivity). *)
Check ASPMonad.getASPSt_ret.
Check ASPMonad.getASPSt_bind.
Check DSLPMonad.getDSLPSt_ret.
Check DSLPMonad.getDSLPSt_bind.

(** l.1632-1648: DSP and ASLP through their parts (partial: relational
    characterizations). *)
Check DSPMonad.getDSPSt_rel.
Check DSPMonad.dspRelSt_bind_of.
Check ASLPMonad.getASLPSt_rel.
Check ASLPMonad.aslpRelSt_bind_of.

(* ================================================================= *)
(** ** Section 3.4, Monads vs. arrows                                *)
(* ================================================================= *)

(** l.1659-1666: the monad laws are proved once from the arrow laws; the
    state and exception arrow transformers preserve the laws, so every
    stateful sp monad is lawful, also with exceptions. *)
Check StateArrowT.Core.ArrowLaws_stateArrT.
Check StateArrowT.ArrowApplyLaws.ArrowApplyLaws_stateArrT.
Check OptionArrowT.ArrowLaws.ArrowLaws_optionArrT.
Check OptionArrowT.ArrowApplyLaws.ArrowApplyLaws_optionArrT.
Check ASPMonad.MonadLawsE_ASPStExc.
Check DSLPMonad.MonadLawsE_DSLPStExc.
Check DSPMonad.MonadLawsE_DSPStExc.
Check ASLPMonad.MonadLawsE_ASLPStExc.

(** l.1667-1669: an arrow morphism gives a monad morphism at a fixed input,
    and lifts through state and exceptions. *)
Check ArrowMorphism.ArrowMorphism.
Check ArrowMorphism.arrow_morphism_monad.
Check ArrowMorphism.state_arrow_morphism.
Check ArrowMorphism.option_arrow_morphism.

(** l.1676-1708: restricted to monotone, strict, disjunctive transformers,
    [StT(ASP)] and [StTArr(ASPArr) unit] are isomorphic through [toArrow]
    and [fromArrow], with the paper's formulas, as ordered monads. *)
Check ASPMonad.toArrowASPState.
Check ASPMonad.fromArrowASPState.
Check ASPMonad.toArrowASPState_formula.
Check ASPMonad.fromArrowASPState_formula.
Check ASPMonad.fromArrowASPState_toArrowASPState.
Check ASPMonad.toArrowASPState_fromArrowASPState.
Check ASPMonad.toArrowASPState_morphism.
Check ASPMonad.fromArrowASPState_morphism.

(* ================================================================= *)
(** ** Section 3.5, Refined wp monads                                *)
(* ================================================================= *)

(** l.1723-1732: the healthiness conditions and the four wp monads AWP,
    DWLP, DWP, AWLP, lawful. *)
Check WPVariants.wpure_strict.
Check WPVariants.wpure_terminating.
Check WPVariants.wpure_conjunctive.
Check WPVariants.wpure_disjunctive.
Check WPVariants.awp_health.
Check WPVariants.dwlp_health.
Check WPVariants.dwp_health.
Check WPVariants.awlp_health.
Check WPVariants.AWP.
Check WPVariants.DWLP.
Check WPVariants.DWP.
Check WPVariants.AWLP.
Check WPVariants.MonadLawsE_AWP.
Check WPVariants.MonadLawsE_DWLP.
Check WPVariants.MonadLawsE_DWP.
Check WPVariants.MonadLawsE_AWLP.

(** l.1723-1725: the four wp monads contain exactly the wps of programs
    under their interpretation: each reading lands in its monad, as a monad
    morphism into it, and every element is the reading of a computation. *)
Check DivNonDet.HealthyReadings.dwpPure_healthy.
Check DivNonDet.HealthyReadings.dwlpPure_healthy.
Check DivNonDet.HealthyReadings.awpPure_healthy.
Check DivNonDet.HealthyReadings.awlpPure_healthy.
Check DivNonDet.HealthyReadings.dwpPure_DWP_morphism.
Check DivNonDet.HealthyReadings.dwlpPure_DWLP_morphism.
Check DivNonDet.HealthyReadings.awpPure_AWP_morphism.
Check DivNonDet.HealthyReadings.awlpPure_AWLP_morphism.
Check DivNonDet.HealthyReadings.dwpPure_DWP_complete.
Check DivNonDet.HealthyReadings.dwlpPure_DWLP_complete.
Check DivNonDet.HealthyReadings.awpPure_AWP_complete.
Check DivNonDet.HealthyReadings.awlpPure_AWLP_complete.

(** l.1734-1738: they share WP's [ret] and [bind]; [ret] has all four
    properties and [bind] preserves each, so they are submonads of WP. *)
Check WPVariants.toWPure_ret.
Check WPVariants.toWPure_bind.
Check WPVariants.wpure_ret_strict.
Check WPVariants.wpure_ret_terminating.
Check WPVariants.wpure_ret_conjunctive.
Check WPVariants.wpure_ret_disjunctive.
Check WPVariants.wpure_bind_strict.
Check WPVariants.wpure_bind_terminating.
Check WPVariants.wpure_bind_conjunctive.
Check WPVariants.wpure_bind_disjunctive.
Check WPVariants.toWPure_morphism.

(* ================================================================= *)
(** ** Section 4.1, Taxonomy of triples                              *)
(* ================================================================= *)

(** l.2747-2763: implication, contrapositive and Galois connection between
    transformers, and what each says of triples. *)
Check TransformerRelations.pt_le.
Check TransformerRelations.pt_le_under.
Check TransformerRelations.pt_le_over.
Check TransformerRelations.Contrapositive.
Check TransformerRelations.Contrapositive_under_over.
Check TransformerRelations.Contrapositive_over_under.
Check TransformerRelations.GaloisPT.
Check TransformerRelations.GaloisPT_over_under.

(** l.2792-2839: Verscht and Kaminski's diagram (their Figure 5) for the
    triples of one stateful monadic program: every implication edge is two
    arrows (under, over), every contrapositive edge two, every Galois edge
    one.  The [Under] triples are named after their logics. *)

(** Implications, correctness side. *)
Check DivNonDetSt.TriplesTaxonomy.TotalCorr_impl_PartCorr.
Check DivNonDetSt.TriplesTaxonomy.TotalCorr_impl_LisbonLogic.
Check DivNonDetSt.TriplesTaxonomy.LisbonLogic_impl_AngPartCorr.
Check DivNonDetSt.TriplesTaxonomy.PartCorr_impl_AngPartCorr.
Check DivNonDetSt.TriplesTaxonomy.dwlp_over_impl_dwp_over.
Check DivNonDetSt.TriplesTaxonomy.awlp_over_impl_awp_over.
Check DivNonDetSt.TriplesTaxonomy.awp_over_impl_dwp_over.
Check DivNonDetSt.TriplesTaxonomy.awlp_over_impl_dwlp_over.

(** Implications, incorrectness side. *)
Check DivNonDetSt.TriplesTaxonomy.aslp_over_impl_asp_over.
Check DivNonDetSt.TriplesTaxonomy.aslp_over_impl_dslp_over.
Check DivNonDetSt.TriplesTaxonomy.asp_over_impl_dsp_over.
Check DivNonDetSt.TriplesTaxonomy.dslp_over_impl_dsp_over.
Check DivNonDetSt.TriplesTaxonomy.DemIncorr_impl_PartIncorr.
Check DivNonDetSt.TriplesTaxonomy.DemIncorr_impl_IncorrLogic.
Check DivNonDetSt.TriplesTaxonomy.PartIncorr_impl_AngPartIncorr.
Check DivNonDetSt.TriplesTaxonomy.IncorrLogic_impl_AngPartIncorr.

(** Contrapositives. *)
Check DivNonDetSt.TriplesTaxonomy.LisbonLogic_contra_dwlp_over.
Check DivNonDetSt.TriplesTaxonomy.AngPartCorr_contra_dwp_over.
Check DivNonDetSt.TriplesTaxonomy.TotalCorr_contra_awlp_over.
Check DivNonDetSt.TriplesTaxonomy.PartCorr_contra_awp_over.
Check DivNonDetSt.TriplesTaxonomy.DemIncorr_contra_aslp_over.
Check DivNonDetSt.TriplesTaxonomy.PartIncorr_contra_asp_over.
Check DivNonDetSt.TriplesTaxonomy.IncorrLogic_contra_dslp_over.
Check DivNonDetSt.TriplesTaxonomy.AngPartIncorr_contra_dsp_over.

(** Galois connections. *)
Check DivNonDetSt.TriplesTaxonomy.PartCorr_galois_asp_over.
Check DivNonDetSt.TriplesTaxonomy.awp_over_galois_PartIncorr.

(* ================================================================= *)
(** ** Section 4.2, Monadic relations (Figure 1)                     *)
(* ================================================================= *)

(** l.2849-2864: DM4all's monadic relation. *)
Check MonadRelation.MonadRelation.

(** l.2881-2890: the stateful wp monads are submonads of [WSt]; the order
    [⊑] on [WSt] is a monadic relation between any two of them. *)
Check WPVariants.toWSt_ret.
Check WPVariants.toWSt_bind.
Check MonadTaxonomy.impliesWSt.
Check MonadTaxonomy.MonadRelation_implies_toWSt.
Check MonadTaxonomy.MonadRelation_impliesWSt.

(** l.2891-2894: what [⊑] between wps says of their triples (partial: the
    text states both directions reversed; these are the correct ones). *)
Check TransformerRelations.pt_le_under.
Check TransformerRelations.pt_le_over.

(** Figure 1(b), wp implication edges (each also with its converse). *)
Check MonadTaxonomy.MonadRelation_dwp_implies_dwlp.
Check MonadTaxonomy.MonadRelation_dwp_implies_awp.
Check MonadTaxonomy.MonadRelation_awp_implies_awlp.
Check MonadTaxonomy.MonadRelation_dwlp_implies_awlp.
Check MonadTaxonomy.MonadRelation_dwlp_implies_dwp.
Check MonadTaxonomy.MonadRelation_awp_implies_dwp.
Check MonadTaxonomy.MonadRelation_awlp_implies_awp.
Check MonadTaxonomy.MonadRelation_awlp_implies_dwlp.

(** l.3005-3018: the four stateful sp monads share [SPSt] and its order;
    [⊑] is not a monadic relation between DSP / ASLP and ASP / DSLP, as
    their binds are not monotone (Figure 2) (partial: shown for the order
    on DSP and on ASLP themselves: no left-unital monotone bind exists). *)
Check MonotoneSPSt.SPStMonotone.SPStMon.
Check MonadTaxonomy.impliesSPSt.
Check DSPMonad.dsp_arbitrary_bind_impossible.
Check ASLPMonad.aslp_arbitrary_bind_impossible.

(** l.3018-3026, Figure 1(b) sp implication edges: the DSP and ASLP binds
    are computed through their components, the relations through the
    components are monadic, and each entails [⊑] of the sps themselves
    (the asterisks). *)
Check SPStBindComparisons.bindDSPSt_SPStMonotone.
Check SPStBindComparisons.bindASLPSt_SPStMonotone.
Check MonadTaxonomy.MonadRelation_dsp_implies_asp.
Check MonadTaxonomy.MonadRelation_dsp_implies_dslp.
Check MonadTaxonomy.MonadRelation_asp_implies_aslp.
Check MonadTaxonomy.MonadRelation_dslp_implies_aslp.
Check MonadTaxonomy.dsp_implies_asp_part.
Check MonadTaxonomy.dsp_implies_dslp_part.
Check MonadTaxonomy.asp_implies_aslp_part.
Check MonadTaxonomy.dslp_implies_aslp_part.

(** l.3036-3057, Figure 1(b) wp contrapositive edges: [⋈] on [WSt] is
    monadic between AWP and DWLP, DWP and AWLP, one to one, and
    symmetric. *)
Check MonadTaxonomy.contraWSt.
Check MonadTaxonomy.MonadRelation_contraWSt.
Check MonadTaxonomy.MonadRelation_contra_awp_dwlp_one.
Check MonadTaxonomy.MonadRelation_contra_awp_dwlp_two.
Check MonadTaxonomy.MonadRelation_contra_dwp_awlp_one.
Check MonadTaxonomy.MonadRelation_contra_dwp_awlp_two.
Check MonadTaxonomy.contra_awp_in_dwlp.
Check MonadTaxonomy.contra_dwlp_in_awp.
Check MonadTaxonomy.contra_dwp_in_awlp.
Check MonadTaxonomy.contra_awlp_in_dwp.
Check MonadTaxonomy.contraWSt_sym.

(** l.3059-3081, Figure 1(b) sp contrapositive edges: [⋈] on [SPSt] is
    monadic between ASP and DSLP, DSP and ASLP, one to one, swapping the
    components and meets with joins; symmetric. *)
Check MonadTaxonomy.contraSPSt.
Check MonadTaxonomy.MonadRelation_contraSPSt.
Check MonadTaxonomy.contraSPSt_meet_join.
Check MonadTaxonomy.contraSPSt_join_meet.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_one.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_two.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_one.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_two.
Check MonadTaxonomy.contra_asp_in_dslp.
Check MonadTaxonomy.contra_dslp_in_asp.
Check MonadTaxonomy.contra_dsp_in_aslp.
Check MonadTaxonomy.contra_aslp_in_dsp.
Check MonadTaxonomy.contraSPSt_sym.

(** l.3088-3108, Figure 1(b) Galois edge ASP -> DWLP: [Ladj] is a monadic
    relation (angelic structure), its sps are disjunctive and strict and
    its wps conjunctive and terminating, it restricts to ASP and DWLP, one
    to one. *)
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj.
Check MonadTaxonomy.GaloisSPWP.
Check MonadTaxonomy.Ladj_GaloisSPWP.
Check MonadTaxonomy.MonadRelation_GaloisSPWP.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_colim.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_lim.
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp.
Check MonadTaxonomy.galois_asp_in_dwlp.
Check MonadTaxonomy.galois_dwlp_in_asp.

(** l.3110-3123, Figure 1(b) Galois edge AWP -> DSLP: [Radj], demonic
    structure, restricts to AWP and DSLP, one to one. *)
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj.
Check MonadTaxonomy.GaloisWPSP.
Check MonadTaxonomy.Radj_GaloisWPSP.
Check MonadTaxonomy.MonadRelation_GaloisWPSP.
Check MonadTaxonomy.MonadRelation_galois_awp_dslp.
Check MonadTaxonomy.galois_awp_in_dslp.
Check MonadTaxonomy.galois_dslp_in_awp.

(** l.3125-3128: contrapositive pairs exchange [Ladj] and [Radj]. *)
Check MonadTaxonomy.Ladj_iff_Radj.

(** Figure 1(a), without state: the wp edges (generic in the two
    conditions), the sp contrapositive and Galois edges, and the collapse
    of DSP into ASP and of ASLP into DSLP. *)
Check MonadTaxonomy.MonadRelation_implies_toWPure.
Check MonadTaxonomy.MonadRelation_contra_toWPure.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_pure.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_pure.
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp_pure.
Check MonadTaxonomy.MonadRelation_galois_awp_dslp_pure.
Check MonadTaxonomy.MonadRelation_dsp_asp_pure.
Check MonadTaxonomy.MonadRelation_aslp_dslp_pure.
Check DSPMonad.dsp_to_asp_morphism.
Check DSPMonad.asp_to_dsp_morphism.
Check ASLPMonad.aslp_to_dslp_morphism.
Check ASLPMonad.dslp_to_aslp_morphism.
Check DSPMonad.asp_to_dsp_to_asp.
Check DSPMonad.dsp_to_asp_to_dsp.
Check ASLPMonad.dslp_to_aslp_to_dslp.
Check ASLPMonad.aslp_to_dslp_to_aslp.

(** Figure 1(a), the sp implication edges ASLP -> ASP and DSLP -> DSP
    without state, through the parts as with state; without state every ASP
    element implies every ASLP element, and every DSP element every DSLP
    element. *)
Check MonadTaxonomy.MonadRelation_asp_implies_aslp_pure.
Check MonadTaxonomy.MonadRelation_dsp_implies_dslp_pure.
Check MonadTaxonomy.asp_implies_aslp_any_pure.
Check MonadTaxonomy.dsp_implies_dslp_any_pure.

(* ================================================================= *)
(** ** Section 4.4, Effect-modularity                                *)
(* ================================================================= *)

(** l.3138-3152: each wp relation is proved on [WPure] and lifted by
    [stateT] (giving exactly the relations on [WSt]) and [optionT]. *)
Check MonadRelation.MonadRelation_stateT.
Check MonadRelation.MonadRelation_optionT.
Check MonadTaxonomy.MonadRelation_impliesWPure.
Check MonadTaxonomy.MonadRelation_contraWPure.
Check MonadTaxonomy.impliesWSt_lift.
Check MonadTaxonomy.contraWSt_lift.
Check MonadTaxonomy.MonadRelation_impliesWStExc.
Check MonadTaxonomy.MonadRelation_contraWStExc.
Check MonadTaxonomy.MonadRelation_implies_WPSubStExc.
Check MonadTaxonomy.MonadRelation_contra_WPSubStExc.

(** l.3156-3171: the arrow transformers; sp relations are proved once at
    arbitrary indices, implication as inclusion and contrapositive as
    equality of the denoted relations, preserved by composition. *)
Check OptionArrowT.Core.optionArrT.
Check MonadTaxonomy.dsp_implies_asp_rel.
Check MonadTaxonomy.dsp_implies_dslp_rel.
Check MonadTaxonomy.asp_implies_aslp_rel.
Check MonadTaxonomy.dslp_implies_aslp_rel.
Check MonadTaxonomy.contra_asp_dslp_rel.
Check MonadTaxonomy.contra_dsp_aslp_rel.
Check MonadRelation.MonadRelation_rel_incl.
Check MonadRelation.MonadRelation_rel_incl_state.
Check MonadRelation.MonadRelation_rel_incl_state_option.
Check MonadRelation.MonadRelation_rel_eq.
Check MonadRelation.MonadRelation_rel_eq_state.
Check MonadRelation.MonadRelation_rel_eq_state_option.

(** l.3173-3177: DSP and ASP (ASLP and DSLP) are told apart by a result
    reachable from two inputs. *)
Check DSPASLPArr.no_ASPArr_for_dsp.
Check DSPASLPArr.no_DSLPArr_for_aslp.

(** l.3178-3181: the exception arrow transformer alone keeps DSP = ASP and
    ASLP = DSLP: the four exception monads, the identity maps as monad
    morphisms both ways, and all four are specification monads. *)
Check ExceptionCollapse.MonadLawsE_DSPExc.
Check ExceptionCollapse.dspExc_to_aspExc_morphism.
Check ExceptionCollapse.aspExc_to_dspExc_morphism.
Check DSPMonad.asp_to_dsp_to_asp.
Check DSPMonad.dsp_to_asp_to_dsp.
Check ExceptionCollapse.aslpExc_to_dslpExc_morphism.
Check ExceptionCollapse.dslpExc_to_aslpExc_morphism.
Check ASLPMonad.dslp_to_aslp_to_dslp.
Check ASLPMonad.aslp_to_dslp_to_aslp.
Check ExceptionCollapse.OrderedMonad_DSPExc.
Check ExceptionCollapse.OrderedMonad_ASLPExc.

(** l.3183-3187: ASP is [SPost_ang], DSLP is [SPost_dem]. *)
Check DSLPMonad.dm4all_dem_to_dslp_morphism.
Check DSLPMonad.dslp_to_dm4all_dem_morphism.
Check DSLPMonad.dm4all_dem_round_trip.
Check DSLPMonad.dslp_dm4all_dem_round_trip.

(** l.3188-3191: [SPost_ang] and [SPost_dem] are isomorphic to [Pred] as
    monads (the angelic maps preserve the order, the demonic ones reverse
    it). *)
Check PredIsomorphisms.pred_to_dm4all_morphism.
Check PredIsomorphisms.dm4all_to_pred_morphism.
Check PredIsomorphisms.dm4all_to_pred_to_dm4all.
Check PredIsomorphisms.pred_to_dm4all_to_pred.
Check PredIsomorphisms.pred_to_dm4all_order.
Check PredIsomorphisms.pred_to_dm4all_dem_morphism.
Check PredIsomorphisms.dm4all_dem_to_pred_morphism.
Check PredIsomorphisms.dm4all_dem_to_pred_to_dm4all_dem.
Check PredIsomorphisms.pred_to_dm4all_dem_to_pred.
Check PredIsomorphisms.pred_to_dm4all_dem_order.

(** l.3192-3195: the adjunctions are proved at the base between [WPure]
    and [Pred], and lifted by [stateT] and [optionT]. *)
Check MonadTaxonomy.MonadRelation_GaloisPredWP.
Check MonadTaxonomy.MonadRelation_GaloisWPPred.
Check MonadTaxonomy.MonadRelation_rel_pred.
Check MonadTaxonomy.MonadRelation_rel_pred_state.
Check MonadTaxonomy.MonadRelation_rel_pred_state_option.
Check MonadTaxonomy.galois_asp_rel.
Check MonadTaxonomy.galois_dslp_rel.

(** l.3197-3200: the diagram again with state and exceptions. *)
Check MonadTaxonomy.MonadRelation_dsp_implies_asp_exc.
Check MonadTaxonomy.MonadRelation_dsp_implies_dslp_exc.
Check MonadTaxonomy.MonadRelation_asp_implies_aslp_exc.
Check MonadTaxonomy.MonadRelation_dslp_implies_aslp_exc.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_exc_one.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_exc_two.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_exc_one.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_exc_two.
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp_exc.
Check MonadTaxonomy.MonadRelation_galois_awp_dslp_exc.

(* ================================================================= *)
(** ** Section 5, Specifying monadic programs                        *)
(* ================================================================= *)

(** l.3247-3293: monad morphisms; triples of a monad morphism, under and
    over; specification of a computation by an element; specification
    monads. *)
Check OrderedMonad.MonadMorphism.
Check Generic.Triple.triple.
Check Generic.Triple.pt_holds.
Check Generic.Triple.Under.
Check Generic.Triple.Over.

(** l.3497-3537: the stateful computation monad and the eight stateful
    morphisms, with their readings on outcomes. *)
Check DivNonDetSt.Computation.stdivndNE.
Check DivNonDetSt.Computation.outSt.
Check DivNonDetSt.Morphisms.dwpSt_morphism.
Check DivNonDetSt.Morphisms.dwlpSt_morphism.
Check DivNonDetSt.Morphisms.awpSt_morphism.
Check DivNonDetSt.Morphisms.awlpSt_morphism.
Check DivNonDetSt.Morphisms.aspSt_morphism.
Check DivNonDetSt.Morphisms.dslpSt_morphism.
Check DivNonDetSt.Morphisms.dspSt_morphism.
Check DivNonDetSt.Morphisms.aslpSt_morphism.
Check DivNonDetSt.Triples.dwpSt_read.
Check DivNonDetSt.Triples.dwlpSt_read.
Check DivNonDetSt.Triples.awpSt_read.
Check DivNonDetSt.Triples.awlpSt_read.
Check DivNonDetSt.Triples.aspSt_read.
Check DivNonDetSt.Triples.dslpSt_read.
Check DivNonDetSt.Triples.dspSt_read.
Check DivNonDetSt.Triples.aslpSt_read.
Check RelSPostArr.dspOf.
Check RelSPostArr.aslpOf.

(** l.3499-3500: the stateful wp morphisms into the refined wp monads. *)
Check DivNonDetSt.HealthyReadings.dwpSt_DWPSt_morphism.
Check DivNonDetSt.HealthyReadings.dwlpSt_DWLPSt_morphism.
Check DivNonDetSt.HealthyReadings.awpSt_AWPSt_morphism.
Check DivNonDetSt.HealthyReadings.awlpSt_AWLPSt_morphism.

(** l.3541-3563: the base wp morphisms, lifted by [stateT] to the stateful
    ones. *)
Check DivNonDet.Morphisms.dwpPure_morphism.
Check DivNonDet.Morphisms.dwlpPure_morphism.
Check DivNonDet.Morphisms.awpPure_morphism.
Check DivNonDet.Morphisms.awlpPure_morphism.
Check Monad.TransformerLaws.MonadMorphism_stateT.
Check DivNonDetSt.Morphisms.wpSt_morphism.

(** l.3566-3599: arrow morphisms into the four base sp arrows (partial:
    from relations, which the computation reaches through [termRel]),
    lifted through state, and the sp monad morphisms they give. *)
Check SPostArrEquiv.asp_from_rel_morphism.
Check SPostArrEquiv.dslp_from_rel_morphism.
Check SPostArrEquiv.dsp_from_rel_morphism.
Check SPostArrEquiv.aslp_from_rel_morphism.
Check DivNonDet.Morphisms.termRel_morphism.
Check DivNonDetSt.Morphisms.spSt_morphism.
Check DivNonDet.Morphisms.aspPure_morphism_rel.
Check DivNonDet.Morphisms.dslpPure_morphism_rel.
Check DivNonDet.Morphisms.dspPure_morphism_rel.
Check DivNonDet.Morphisms.aslpPure_morphism_rel.

(** l.3614-3653: sp triples; each edge of Figure 1(b) relates the
    transformers ([_pt]), hence the triples (Section 4.1; examples:
    ASLP -> ASP, ASP -- DSLP, ASP -> DWLP); incorrectness logic and Lisbon
    logic. *)
Check MonadTaxonomy.impliesWSt_pt.
Check MonadTaxonomy.impliesSPSt_pt.
Check MonadTaxonomy.contraWSt_pt.
Check MonadTaxonomy.contraSPSt_pt.
Check MonadTaxonomy.GaloisSPWP_pt.
Check MonadTaxonomy.GaloisWPSP_pt.
Check DivNonDetSt.Triples.triple_aspSt.
Check DivNonDetSt.Triples.triple_awpSt.

(** l.3657-3705: the running program on even and odd states, its AWP and
    ASP transformers; Lisbon logic fails (at [s = 1]) where incorrectness
    logic holds; with [p'] both hold. *)
Check ResetEven.m.
Check ResetEven.m_out.
Check ResetEven.awp_m.
Check ResetEven.asp_m.
Check ResetEven.awp_m_q.
Check ResetEven.asp_m_p.
Check ResetEven.lisbon_p_q_fails.
Check ResetEven.incorr_p_q.
Check ResetEven.asp_m_p'.
Check ResetEven.lisbon_p'_q.
Check ResetEven.incorr_p'_q.

(** l.3707-3726: the wp triple sequencing rule, under and over, for any
    monad morphism into the stateful wp monad, hence for the four readings
    (all eight kinds). *)
Check DivNonDetSt.TripleRules.wpSt_bind_under.
Check DivNonDetSt.TripleRules.wpSt_bind_over.

(** l.3728-3735: the ASP and DSLP rules in both directions (Hoare logic
    and incorrectness logic), and DSP under / ASLP over through their
    components (partial: the side condition [q0 ⇒ p_a] is right for the
    over-approximate rules; the under-approximate ones need [p_a ⇒ q0];
    under-approximate ASP and over-approximate DSLP, with a family of
    [p_a], also need an inhabited result type). *)
Check DivNonDetSt.TripleRules.aspSt_bind_over.
Check DivNonDetSt.TripleRules.aspSt_bind_under.
Check DivNonDetSt.TripleRules.dslpSt_bind_under.
Check DivNonDetSt.TripleRules.dslpSt_bind_over.
Check DivNonDetSt.TripleRules.dspSt_under_iff.
Check DivNonDetSt.TripleRules.aslpSt_over_iff.
Check DivNonDetSt.TripleRules.dspSt_bind_under.
Check DivNonDetSt.TripleRules.aslpSt_bind_over.
Check DSPSequencing.side_aspSt_under.
Check DSPSequencing.inhabited_aspSt_under.

(** l.3737-3749 (Figure 2): over-approximate DSP and under-approximate ASLP
    triples do not compose; the counterexample (b) is the complement of
    (a). *)
Check DSPSequencing.dspSt_over_seq_counterexample.
Check DSPSequencing.aslpSt_under_seq_counterexample.

(** l.3797-3812: the comparison rule is the bind typing of the Dijkstra
    monad of a morphism; ASP, DSLP and the wp monads are specification
    monads; DSP and ASLP are not (Section 1). *)
Check DijkstraMonad.DM_bind_typing.
Check ASPMonad.OrderedMonad_ASP.
Check ASPMonad.OrderedMonad_ASPSt.
Check DSLPMonad.OrderedMonad_DSLP.
Check DSLPMonad.OrderedMonad_DSLPSt.
Check WPVariants.OrderedMonad_DWPSt.
Check WPVariants.OrderedMonad_AWPSt.
Check WPVariants.OrderedMonad_DWLPSt.
Check WPVariants.OrderedMonad_AWLPSt.

(** l.3817-3839: the AWP specification of the running program, its
    comparison (a Dijkstra-monad typing), and its equivalence with the
    pre/post pair. *)
Check ResetEven.wspec.
Check ResetEven.awp_m_le_wspec.
Check ResetEven.m_DM.
Check ResetEven.wspec_pp2wp.
Check ResetEven.le_wspec_iff_lisbon.

(** l.3843-3883: wp triples, ASP over and DSLP under triples embed as
    specifications ([pp2wp_under], [pp2wp_over], [pp2asp_over],
    [pp2dslp_under]) (partial: the wp comparisons are in DM4all's order
    [WP_le], the converse of the paper's l.868-872 order). *)
Check DivNonDetSt.Typings.wpUnderSt.
Check DivNonDetSt.Typings.wpOverSt.
Check DivNonDetSt.Typings.triple_under_wpSt.
Check DivNonDetSt.Typings.triple_over_wpSt.
Check Generic.Typings.aspOver.
Check Generic.Typings.dslpUnder.
Check Generic.Typings.le_aspOver.
Check Generic.Typings.le_dslpUnder.
Check DivNonDetSt.Typings.triple_over_aspSt.
Check DivNonDetSt.Typings.triple_under_dslpSt.

(** l.3885-3919: no specification embeds ASP under (nor DSLP over)
    triples; an ASP specification may still match a triple, but typing at
    it is strictly stronger than the triple. *)
Check DivNonDetSt.Typings.no_asp_under_index.
Check DivNonDetSt.Typings.no_dslp_over_index.
Check Generic.Typings.le_aspUnder.
Check Generic.Typings.aspUnder_typing_triple.
Check DijkstraExamples.progA_Dasp_op.
Check DijkstraExamples.progloom_harder_not_Dasp_op.

(** l.3944-3974: the Dijkstra monad of a monad morphism, its operations
    and DM4all's laws; also with the order flipped. *)
Check DijkstraMonad.OrderedTarget.
Check DijkstraMonad.DM.
Check DijkstraMonad.DM_ret.
Check DijkstraMonad.DM_bind.
Check DijkstraMonad.DM_wkn.
Check DijkstraMonad.DijkstraLaws.
Check DijkstraMonad.DM_laws.
Check DijkstraMonad.DMop.
Check DijkstraMonad.DMop_laws.

(** l.3974-3993: Dijkstra monads for the four wp monads, ASP and DSLP
    (with state; with exceptions, with their laws), and the verified
    examples as their elements (partial: one example per Dijkstra monad). *)
Check DivNonDetSt.DijkstraMonads.OrderedTarget_dwpSt.
Check DivNonDetSt.DijkstraMonads.OrderedTarget_dwlpSt.
Check DivNonDetSt.DijkstraMonads.OrderedTarget_awpSt.
Check DivNonDetSt.DijkstraMonads.OrderedTarget_awlpSt.
Check DivNonDetSt.DijkstraMonads.OrderedTarget_aspSt.
Check DivNonDetSt.DijkstraMonads.OrderedTarget_dslpSt.
Check DivNonDetStExc.DijkstraMonads.Ddwp_laws.
Check DivNonDetStExc.DijkstraMonads.Ddwlp_laws.
Check DivNonDetStExc.DijkstraMonads.Dawp_laws.
Check DivNonDetStExc.DijkstraMonads.Dawlp_laws.
Check DivNonDetStExc.DijkstraMonads.Dasp_laws.
Check DivNonDetStExc.DijkstraMonads.Ddslp_laws.
Check DijkstraExamples.progA_Ddwp.
Check DijkstraExamples.progB_Ddwlp.
Check DijkstraExamples.progA_Dawp.
Check DijkstraExamples.progB_Dawlp.
Check DijkstraExamples.progA_Dasp.
Check DijkstraExamples.progEx_Ddslp_op.

(* ================================================================= *)
(** ** Section 6, Galois connections between specification monads    *)
(* ================================================================= *)

(** l.4099-4120: DM4all's Galois connections between [Pred], [PrePost] and
    [WP] (diagram); [Pred] is a specification monad. *)
Check PredMonad.OrderedMonad_Pred.
Check BaseGaloisConnections.pred_pp_adjunction.
Check BaseGaloisConnections.wp_pp_under_adjunction.
Check BaseGaloisConnections.wp_pp_over_adjunction.

(** l.4109-4120, the [SPost] -- [Pred] edge of the diagram (partial: for
    binary arrows, monotone sps and relations, at input [unit]). *)
Check GaloisArr.Galois_Rel_SPost.

(** l.4124-4126: in the pure case [SPost ~ Pred] (Section 4.4 above). *)
Check PredIsomorphisms.pred_to_dm4all_morphism.

(** l.4130-4134: monotone monad transformers preserve Galois connections
    (partial: they preserve monadic relations, which the Galois connections
    are in Section 4). *)
Check MonadRelation.MonadRelation_stateT.
Check MonadRelation.MonadRelation_optionT.

(** l.4262-4316: the stateful [Pred]; [φ] and [ψ] are monad morphisms
    (angelic structure); [Ladj (φ p) (ψ p)], and every [Ladj] pair is of
    this form; [φ ⊣ φ'] and [φ'] preserves the angelic structure (the
    paper says demonic); the adjoints are colimit/limit preserving; ASP is
    isomorphic to DWLP. *)
Check PredMonad.PredSt.PredSt.
Check PredMonad.PredSt.ordPredSt.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_ret.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_bind.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_ret.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_bind.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_fromPred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_pred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_toPred_adj.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_ret.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_bind.
Check MonadTaxonomy.galois_asp_dwlp_order.
Check SPostArrEquiv.asp_to_rel_morphism.

(** l.4325-4379: the demonic side: [ξ] (monotone into [Pred^op]), [ζ],
    [ξ']; [ξ' ⊣ ξ]; [ξ] and [ζ] are monad morphisms (demonic structure);
    the lax demonic bind (footnote); [Radj (ξ p) (ζ p)], and every [Radj]
    pair is of this form; nuclei and limits; DSLP is isomorphic to AWP. *)
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_antitone.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.toPred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_toPred_adj.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_ret.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_bind.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_ret.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_bind.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.bindP.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.lunit.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.runit.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.assoc.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_fromPred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_pred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_toPred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.tPfP_unit.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.tPfP_unit_inv.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_unit.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_unit_inv.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_lim.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_colim.
Check MonadTaxonomy.galois_awp_dslp_order.
Check SPostArrEquiv.dslp_to_rel_morphism.

(* ================================================================= *)
(** ** Section 7, Formalization in Rocq                              *)
(* ================================================================= *)

(** l.4428-4430: example programs that together use all sixteen kinds of
    triples (index: [Verification/DivNonDetStExc/TriplesExamples.v]). *)
Check ProgA.progA_dwp_under.
Check ProgRet.progRet_dwp_over.
Check ProgB.progB_dwlp_under.
Check ProgRet.progRet_dwlp_over.
Check ProgA.progA_awp_under.
Check ProgA.progA_awp_over.
Check ProgB.progB_awlp_under.
Check ProgRet.progRet_awlp_over.
Check ProgA.progA_asp_under.
Check ProgA.progA_asp_over.
Check ProgEx.progEx_dslp_under.
Check ProgA.progA_dslp_over.
Check ProgRet.progRet_dsp_under.
Check ProgRet.progRet_dsp_over.
Check ProgRet.progRet_aslp_under.
Check ProgRet.progRet_aslp_over.

(** l.4431-4432: programs written as interaction trees, mapped into the
    computation monad by a monad morphism. *)
Check DivNonDet.Computation.denote_morphism.
Check DivNonDetSt.Computation.denoteSt_morphism.
Check DivNonDetStExc.Computation.denoteStExc_morphism.

(** l.4437-4442: all sp arrows are choice arrows, with Hughes's laws and
    Paterson's distribution law; the transformers preserve them (partial:
    the sentence also says loop arrows, which they are not: no sp arrow
    has an [ArrowLoop] instance). *)
Check Arrow.ArrowChoiceLaws.
Check SPostArr.ArrowChoiceLaws_ASPArr.
Check SPostArr.ArrowChoiceLaws_DSLPArr.
Check DSPASLPArr.ArrowChoiceLaws_DSPArr.
Check DSPASLPArr.ArrowChoiceLaws_ASLPArr.
Check StateArrowT.ArrowChoiceLaws.ArrowChoiceLaws_stateArrT.
Check OptionArrowT.ArrowChoiceLaws.ArrowChoiceLaws_optionArrT.

(** Not checkable here: l.4412-4413, "about 28k lines", "only funext,
    propext and excluded middle" (the build has about 38.6k lines;
    [Checks/Assumptions.v] reports the axioms, which also include
    [eq_rect_eq], through ITree). *)

(* ================================================================= *)
(** ** Appendix A, Arrow laws                                        *)
(* ================================================================= *)

(** l.4537-4557: the twelve laws, with logical equivalence of sp arrows as
    the equality. *)
Check Arrow.ArrowLaws.
Check Arrow.ArrowApplyLaws.
Check SPostArr.ASPArr_eq.
Check SPostArr.DSLPArr_eq.
Check DSPASLPArr.DSPArr_eq.
Check DSPASLPArr.ASLPArr_eq.

(* ================================================================= *)
(** ** Appendix B, The DSP and ASLP arrows                           *)
(* ================================================================= *)

(** l.4561-4645: the two arrows, their parts, operations and laws; direct
    composition of dsps fails (partial: on non-pure arrows; the parts are
    defined through the relation an element denotes, not by the displayed
    formulas); at input [unit] they give DSP and ASLP. *)
Check DSPASLPArr.DSPArr.
Check DSPASLPArr.pure_DSP.
Check DSPASLPArr.comp_DSP.
Check DSPASLPArr.first_DSP.
Check DSPASLPArr.app_DSP.
Check DSPASLPArr.ArrowLaws_DSPArr.
Check DSPASLPArr.ArrowApplyLaws_DSPArr.
Check SPostArrInfrastructure.dsp_naive_transformer_comp_rejects.
Check DSPASLPArr.ASLPArr.
Check DSPASLPArr.pure_ASLP.
Check DSPASLPArr.comp_ASLP.
Check DSPASLPArr.first_ASLP.
Check DSPASLPArr.app_ASLP.
Check DSPASLPArr.ArrowLaws_ASLPArr.
Check DSPASLPArr.ArrowApplyLaws_ASLPArr.
Check DSPMonad.dspsp_to_dsp_morphism.
Check DSPMonad.dsp_to_dspsp_morphism.
Check ASLPMonad.aslpsp_to_aslp_morphism.
Check ASLPMonad.aslp_to_aslpsp_morphism.
Check DSPMonad.dspsp_to_dsp_to_dspsp.
Check DSPMonad.dsp_to_dspsp_to_dsp.
Check ASLPMonad.aslpsp_to_aslp_to_aslpsp.
Check ASLPMonad.aslp_to_aslpsp_to_aslp.

(* ================================================================= *)
(** ** Appendix C, Fixing the input of the ASP and DSLP arrows       *)
(* ================================================================= *)

(** l.4647-4732: Lemma lem:asp-singleton; fixing the input of [ASPArr]
    gives the carrier and the [ret] and [bind] of [ASP] (partial: [bind]
    read in relational form; the carrier equivalence is proved
    classically, not constructively). *)
Check ASPMonad.getASP_singleton.
Check ASPMonad.join_iff_singleton.
Check ASPMonad.getASP_ret.
Check ASPMonad.getASP_bind.
Check ASPMonad.aspsp_to_asp_morphism.

(** l.4733-4786: dually Lemma lem:dslp-singleton, and the [ret] and [bind]
    of [DSLP] (partial: [bind] read in relational form). *)
Check DSLPMonad.getDSLP_msingleton.
Check DSLPMonad.meet_iff_msingleton.
Check DSLPMonad.getDSLP_ret.
Check DSLPMonad.getDSLP_bind.
Check DSLPMonad.dslpsp_to_dslp_morphism.

(* ================================================================= *)
(** ** Appendix D, Counterexamples to the monad and arrow laws       *)
(* ================================================================= *)

(** l.4810-4854, D.1: [SPost_ang(S, A)] (monotone, strict) with the
    (ang-st) operations: the unit laws hold, associativity fails, with the
    paper's [m], [f], [g] (at [S = A = bool]). *)
Check StatefulSPostCounterexample.St.SPostSt.
Check StatefulSPostCounterexample.St.SPostSt_bind_ret_r.
Check StatefulSPostCounterexample.St.SPostSt_bind_ret_l.
Check StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails.

(** l.4856-4886, D.2: [SPost_dem(S, A)] (monotone, terminating) with the
    (dem-st) operations: the unit laws hold, associativity fails, with the
    paper's [m], [f], [g] (at [S = A = bool]). *)
Check StatefulSPostCounterexample.Dem.SPostDem.
Check StatefulSPostCounterexample.Dem.SPostDem_bind_ret_r.
Check StatefulSPostCounterexample.Dem.SPostDem_bind_ret_l.
Check StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails.

(** l.4888-4927, D.3: the monotone, strict sp arrows with the operations of
    [ASPArr] (the codomain condition amounts to strictness) fail
    [first f >>> arr fst = arr fst >>> f], with the paper's [g] and [pre];
    dually for the monotone, terminating arrows with those of [DSLPArr]. *)
Check LawCounterexamples.AngArr.SPArrAng.
Check LawCounterexamples.AngArr.codomain_iff_strict.
Check LawCounterexamples.AngArr.compAng_ASP.
Check LawCounterexamples.AngArr.first_fst_fails.
Check LawCounterexamples.AngArr.not_ArrowLaws.
Check LawCounterexamples.DemArr.SPArrDem.
Check LawCounterexamples.DemArr.codomain_iff_terminating.
Check LawCounterexamples.DemArr.compDem_DSLP.
Check LawCounterexamples.DemArr.first_fst_fails.
Check LawCounterexamples.DemArr.not_ArrowLaws.

(* ================================================================= *)
(** ** Appendix E, Decomposing dsp and aslp transformers             *)
(* ================================================================= *)

(** l.4929-5086: Lemmas lem:dsp-split and lem:aslp-split, and the health
    of the components (partial: the components are defined through the
    relation an element denotes, not by the displayed formulas; their health
    holds by their types). *)
Check DSPASLPArr.dsp_split.
Check DSPASLPArr.aspPartArr.
Check DSPASLPArr.dslpPartArr.
Check DSPASLPArr.aslp_split.
Check DSPASLPArr.aspPartAArr.
Check DSPASLPArr.dslpPartAArr.
