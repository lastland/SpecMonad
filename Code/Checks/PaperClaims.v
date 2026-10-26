(** * Paper claims index

    One block per section of the paper, in paper order.  Each block quotes
    or paraphrases a claim and names the Rocq objects that state it:
    [Print] for definitions, so their body shows, and [Check] for theorems.
    This file holds only what the paper claims.
    Assumptions are reported by [Checks/Assumptions.v]. *)

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
  LawCounterexamples.
From Incorrectness.PTMonadTaxonomy Require
  TransformerRelations MonotoneSPSt SPStBindComparisons MonadTaxonomy.
From Incorrectness.Verification.Generic Require
  Triple DijkstraMonad Typings.
From Incorrectness.Verification.DivNonDet Require
  Computation Morphisms Triples TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetSt Require
  Computation Morphisms Triples TriplesTaxonomy Typings DijkstraMonads.
From Incorrectness.Verification.DivNonDetSt.TriplesExamples Require
  ResetEven IncorrectnessLogic.
From Incorrectness.Verification.DivNonDetStExc Require
  Computation Morphisms DijkstraMonads TriplesExamples DijkstraExamples.
From Incorrectness.GaloisConnections Require
  BaseGaloisConnections GaloisArr.
From Incorrectness.Tests Require
  SPostArrInfrastructure.
From Incorrectness.Verification.DivNonDetStExc Require Triples.

Import Incorrectness.Verification.DivNonDet.Triples
  Incorrectness.Verification.DivNonDetSt.Triples
  Incorrectness.Verification.DivNonDetStExc.Triples.

(* ================================================================= *)
(** ** Section 1, Introduction                                       *)
(* ================================================================= *)

(** Claims of the introduction that later sections do not restate.  The
    contribution bullets are backed in the sections they point to. *)

(** Partial correctness is [p => dwlp c q], equivalently
    [asp c p => q]; incorrectness logic is [q => asp c p] (for monadic
    stateful programs; [PartCorr], [IncorrLogic] are the named triples). *)
Check DivNonDetSt.TriplesTaxonomy.PartCorr_galois_asp_over.
Check DivNonDetSt.Triples.triple_aspSt.

(** The state transformer on the wp monad. *)
Print WPure.WSt.
Check WPure.MonadLawsE__WSt.

(** "monotone sps alone do not form a lawful monad" (partial: for
    the angelic structure on monotone stateful transformers, left unit holds
    only as an inequation; the converse fails for an inhabited state). *)
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.lunitStrictlyLax.

(** Maillard et al.'s [SPost] specifies programs under the angelic,
    total interpretation: it is isomorphic to [ASP] as a monad. *)
Check ASPMonad.dm4all_to_asp_morphism.
Check ASPMonad.asp_to_dm4all_morphism.
Check ASPMonad.dm4all_round_trip.
Check ASPMonad.asp_dm4all_round_trip.

(** The four homomorphism properties of sps. *)
Print PredicateTransformerProperties.StrictArr.
Print PredicateTransformerProperties.TerminatingArr.
Print PredicateTransformerProperties.ConjunctiveArr.
Print PredicateTransformerProperties.DisjunctiveArr.

(** A specification monad is a monad ordered so that [bind] is
    monotone. *)
Print OrderedMonad.OrderedMonad.

(** The base computation monad of nondeterminism and
    nontermination. *)
Print DivNonDet.Computation.divndNE.

(** State and exceptions on both sides, lawful; the morphisms
    lift for free. *)
Check ASPMonad.MonadLawsE_ASPStExc.
Check DSLPMonad.MonadLawsE_DSLPStExc.
Check DSPMonad.MonadLawsE_DSPStExc.
Check ASLPMonad.MonadLawsE_ASLPStExc.
Check Monad.TransformerLaws.MonadMorphism_optionT.
Check ArrowMorphism.state_option_arrow_morphism.
Check DivNonDetStExc.Morphisms.dwpStExc_morphism.
Check DivNonDetStExc.Morphisms.aspStExc_morphism_rel.
Check DivNonDetStExc.Morphisms.dspStExc_morphism_rel.

(** Simple programs proved to satisfy correctness and
    incorrectness triples: the examples indexed in
    [Verification/DivNonDetStExc/TriplesExamples.v]. *)

(** asp, dslp and all wp monads are specification monads, also
    with exceptions; flipping the order covers over- and
    under-approximation. *)
Check ASPMonad.OrderedMonad_ASPStExc.
Check DSLPMonad.OrderedMonad_DSLPStExc.
Check WPure.OrderedMonad_WStExc.
Check OrderedMonad.OrderedMonad_flip.

(** The stateful dsp and aslp binds are not monotone.  Which
    triples embed as Dijkstra-monad specifications: asp over and dslp
    under do, asp under and dslp over do not; backed in Section 5. *)
Check DSPMonad.not_OrderedMonad_DSPSt.
Check ASLPMonad.not_OrderedMonad_ASLPSt.
Check DSPMonad.not_OrderedMonad_DSPStExc.
Check ASLPMonad.not_OrderedMonad_ASLPStExc.

(** Galois connections with stateful [Pred] (Section 6) and
    pre/post specifications (partial: as Galois connections of binary
    arrows, at input [S]). *)
Print GaloisArr.Galois_Rel_PrePost.
Print GaloisArr.Galois_WP_PrePost.

(** The isomorphism between [Pred] and [SPost] extends to
    isomorphisms between asp and dwlp and between dslp and awp as stateful
    specification monads: the nuclei of Section 6 put each of the four in
    bijection with the stateful predicates, the maps preserve [ret] and
    [bind], and the Galois relations carry one order to the other. *)
Check MonadTaxonomy.galois_asp_dwlp_order.
Check MonadTaxonomy.galois_awp_dslp_order.
Check MonadTaxonomy.sp_disj_strict_is_asp.
Check MonadTaxonomy.wp_conj_term_is_dwlp.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.tPfP_unit_inv.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_fix_disj_strict.

(* ================================================================= *)
(** ** Section 2, Background: weakest precondition monads            *)
(* ================================================================= *)

(** The monotone continuation monad on [P], with its [ret] and
    [bind]; monotonicity, preserved by [ret] and [bind]. *)
Print WPure.WPure.
Print WPure.wpure_mono.
Print WPure.retWPure.
Print WPure.bindWPure.
Check WPure.MonadLawsE_WPure.
Check WPVariants.wpure_ret_mono.
Check WPVariants.wpure_bind_mono.

(** The pointwise order, preserved by [ret] and [bind]
    ([WP_le] is DM4all's direction, the converse of the paper's). *)
Print WPure.WP_le.
Check WPure.OrderedMonad_WPure.

(** The stateful wp monad, ordered, with monotone [bind]. *)
Print WPure.retPs.
Print WPure.bindPs.
Print WPure.ordWSt.
Check WPure.OrderedMonad_WSt.

(* ================================================================= *)
(** ** Section 3.1, Base sp monads                                   *)
(* ================================================================= *)

(** An sp of a pure program, [P -> (A -> P)]. *)
Print RawSP.SPPure.

(** Maillard et al.'s [SPost] (monotone, postconditions imply
    the precondition), with (ang) [ret]/[bind], is lawful. *)
Print SPostMonad.SPM.SPost.
Print SPostMonad.SPM.retSP.
Print SPostMonad.SPM.bindSP.
Check SPostMonad.SPMFacts.MonadLawsE_SPost.
Print SPostMonad.SPostPure.

(** That carrier is the disjunctive, strict sps. *)
Check ASPMonad.monotone_codomain_iff_singleton.
Check ASPMonad.join_iff_singleton.

(** Disjunctivity, strictness, conjunctivity,
    termination of base sps. *)
Print RawSP.Disjunctive.
Print RawSP.Strict.
Print RawSP.Conjunctive.
Print RawSP.Terminating.

(** [ASP], the sps preserving all disjunctions, with (ang)
    [ret]/[bind], lawful. *)
Print ASPMonad.ASPSP.
Print ASPMonad.retASPSP.
Print ASPMonad.bindASPSP.
Check ASPMonad.MonadLawsE_ASPSP.

(** Without disjunctivity (conjunctivity) the associativity
    of the stateful bind fails (Appendix E). *)
Check StatefulSPostCounterexample.FailingBind.SPostStExc_bind_bind_fails.
Check StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails.
Check StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails.

(** Each class is exactly the transformers of programs under
    its interpretation (at the arrow level). *)
Check SPostArr.asp_join_iff.
Check SPostArr.dslp_meet_iff.
Check DSPASLPArr.dsp_hom_iff.
Check DSPASLPArr.aslp_hom_iff.

(** Keeping the (ang) [ret] and [bind] on the conjunctive,
    terminating carrier does not give DSLP: the [ret] already leaves that
    carrier, which settles it without looking at [bind].  Stated for
    dm4all's [retSP], the (ang) [ret] transported along the isomorphism
    proved in the same file. *)
Check ASPMonad.dm4all_not_dslp_healthy.

(** [DSLP] with (dem) [ret]/[bind] is lawful. *)
Print DSLPMonad.DSLPSP.
Print DSLPMonad.retDSLPSP.
Print DSLPMonad.bindDSLPSP.
Check DSLPMonad.MonadLawsE_DSLPSP.
Check DSLPMonad.meet_iff_msingleton.

(** [DSP] (conjunctive, strict) and [ASLP] (disjunctive,
    terminating); each element is the meet (join) of its [aspOf] and
    [dslpOf] parts; both monads are lawful.  The parts are defined through
    the relation an element denotes; [aspPart_formula] &c. show they agree
    with the formulas displayed in the paper (Section 3.1 for DSP,
    Appendix F.2 for ASLP), which are classical. *)
Print DSPMonad.DSP.
Print DSPASLPArr.dspRel.
Print DSPASLPArr.aspPartArr.
Print DSPASLPArr.dslpPartArr.
Check DSPASLPArr.aspPart_formula.
Check DSPASLPArr.dslpPart_formula.
Check DSPASLPArr.dsp_split.
Check DSPMonad.MonadLawsE_DSP.
Print ASLPMonad.ASLP.
Print DSPASLPArr.aslpRel.
Print DSPASLPArr.aspPartAArr.
Print DSPASLPArr.dslpPartAArr.
Check DSPASLPArr.aspPartA_formula.
Check DSPASLPArr.dslpPartA_formula.
Check DSPASLPArr.aslp_split.
Check ASLPMonad.MonadLawsE_ASLP.

(** "the stateful dsp and aslp monads have binds that are not
    monotone": checked in the Section 1 block above. *)

(** The four pure sp monads. *)
Check ASPMonad.MonadLawsE_ASP.
Check DSLPMonad.MonadLawsE_DSLP.

(** The state monad transformer on a lawful monad is lawful
    (partial: generic; [stateT S SPost] itself is not defined). *)
Check Monad.TransformerLaws.MonadLawsE_stateT.

(* ================================================================= *)
(** ** Section 3.2, Base sp arrows                                   *)
(* ================================================================= *)

(** Arrows, application, and the monad of an arrow with
    application at a fixed input. *)
Print Arrow.Arrow.
Print Arrow.ArrowApply.
Print ArrowMonad.Monad_Arrow.

(** sp arrows [(B -> P) -> (A -> P)], monotone. *)
Print SPostArr.SPArrT.
Print SPostArr.sp_monotone.

(** [ASPArr] (strict + disjunctive = all disjunctions), its
    operations, lawful; at input [unit] it is [ASP]. *)
Print SPostArr.ASPArr.
Check PredicateTransformerProperties.strict_disjunctiveArr_full_join.
Check SPostArr.ASP_full_join.
Print SPostArr.pureASP.
Print SPostArr.compASP.
Print SPostArr.firstASP.
Print SPostArr.appASP.
Check SPostArr.ArrowLaws_ASPArr.
Check SPostArr.ArrowApplyLaws_ASPArr.
Print ASPMonad.ASP.
Check ASPMonad.aspsp_to_asp_morphism.
Check ASPMonad.asp_to_aspsp_morphism.
Check ASPMonad.aspsp_to_asp_to_aspsp.
Check ASPMonad.asp_to_aspsp_to_asp.

(** Monotonicity and strictness alone are not enough: without
    disjunctivity the arrow laws fail (Appendix E.3; dually without
    conjunctivity). *)
Check LawCounterexamples.AngArr.not_ArrowLaws.
Check LawCounterexamples.DemArr.not_ArrowLaws.

(** [DSLPArr] (terminating + conjunctive = all conjunctions),
    its operations, lawful; at input [unit] it is [DSLP]. *)
Print SPostArr.DSLPArr.
Check PredicateTransformerProperties.terminating_conjunctiveArr_full_meet.
Check SPostArr.DSLP_full_meet.
Print SPostArr.pureDSLP.
Print SPostArr.compDSLP.
Print SPostArr.firstDSLP.
Print SPostArr.appDSLP.
Check SPostArr.ArrowLaws_DSLPArr.
Check SPostArr.ArrowApplyLaws_DSLPArr.
Print DSLPMonad.DSLP.
Check DSLPMonad.dslpsp_to_dslp_morphism.
Check DSLPMonad.dslp_to_dslpsp_morphism.
Check DSLPMonad.dslpsp_to_dslp_to_dslpsp.
Check DSLPMonad.dslp_to_dslpsp_to_dslp.

(* ================================================================= *)
(** ** Section 3.3, Stateful sp arrows and monads                    *)
(* ================================================================= *)

(** A lawful arrow with application gives a lawful monad at a
    fixed input; the state arrow transformer preserves the laws and gives
    the four stateful sp monads. *)
Check ArrowMonad.MonadLawsE_Arrow.
Print StateArrowT.Core.stateArrT.
Print ASPMonad.ASPSt.
Check ASPMonad.MonadLawsE_ASPSt.
Print DSLPMonad.DSLPSt.
Check DSLPMonad.MonadLawsE_DSLPSt.
Print DSPMonad.DSPSt.
Check DSPMonad.MonadLawsE_DSPSt.
Print ASLPMonad.ASLPSt.
Check ASLPMonad.MonadLawsE_ASLPSt.
Check StateArrowT.Core.ArrowLaws_stateArrT.
Check StateArrowT.ArrowApplyLaws.ArrowApplyLaws_stateArrT.

(** The unfolded stateful [ret]/[bind] of ASP and DSLP, in the relational
    form and in the displayed form of (ang-st) resp. (dem-st). *)
Check ASPMonad.getASPSt_ret.
Check ASPMonad.getASPSt_bind.
Check ASPMonad.getASPSt_bind_formula.
Check DSLPMonad.getDSLPSt_ret.
Check DSLPMonad.getDSLPSt_bind.
Check DSLPMonad.getDSLPSt_bind_formula.

(* ================================================================= *)
(** ** Section 3.4, Monads vs. arrows                                *)
(* ================================================================= *)

(** An arrow morphism gives a monad morphism once the input is
    fixed, and the arrow transformers lift arrow morphisms. *)
Print ArrowMorphism.ArrowMorphism.
Check ArrowMorphism.arrow_morphism_monad.
Check ArrowMorphism.state_arrow_morphism.
Check ArrowMorphism.option_arrow_morphism.

(** Restricted to monotone, strict, disjunctive transformers,
    the carriers of [StT(ASP)] and [StTArr(ASPArr) unit] are isomorphic
    through [toArrow] and [fromArrow], with the paper's formulas. *)
Print ASPMonad.toArrowASPState.
Print ASPMonad.fromArrowASPState.
Check ASPMonad.toArrowASPState_formula.
Check ASPMonad.fromArrowASPState_formula.
Check ASPMonad.fromArrowASPState_toArrowASPState.
Check ASPMonad.toArrowASPState_fromArrowASPState.

(* ================================================================= *)
(** ** Section 3.5, Refined wp monads                                *)
(* ================================================================= *)

(** The healthiness conditions and the four wp monads AWP,
    DWLP, DWP, AWLP, lawful. *)
Print WPVariants.wpure_strict.
Print WPVariants.wpure_terminating.
Print WPVariants.wpure_conjunctive.
Print WPVariants.wpure_disjunctive.
Check WPVariants.awp_health.
Check WPVariants.dwlp_health.
Check WPVariants.dwp_health.
Check WPVariants.awlp_health.
Print WPVariants.AWP.
Print WPVariants.DWLP.
Print WPVariants.DWP.
Print WPVariants.AWLP.
Check WPVariants.MonadLawsE_AWP.
Check WPVariants.MonadLawsE_DWLP.
Check WPVariants.MonadLawsE_DWP.
Check WPVariants.MonadLawsE_AWLP.

(** They share WP's [ret] and [bind]; [ret] has all four
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

(** Each of the four readings of a computation lands in the refined monad
    of its interpretation, and corestricts to a monad morphism into it
    ([corestrict], [corestrict_morphism]); with state these are the
    [stateT_map] lifts.  So the morphisms of Section 5 target the four wp
    monads, not only the ambient [WPure].  Conversely, classically, every
    element of a refined monad is the reading of a computation
    ([dwpPure_DWP_complete] &c.), so the four contain exactly the wps of
    programs under their interpretation.  With state and exceptions the
    refined monads are [WPSubStExc] = [stateT S (optionT (WPSub h))],
    ordered and lawful through the generic transformers; both directions
    lift to the two stacks, completeness pointwise in the start state
    ([dwpSt_DWPSt_complete], [dwpStExc_DWPStExc_complete] &c.). *)
Print WPVariants.corestrict.
Check WPVariants.corestrict_morphism.
Check WPVariants.conjunctive_repr.
Check WPVariants.disjunctive_repr.
Check DivNonDet.Morphisms.dwpPure_into_dwp.
Check DivNonDet.Morphisms.dwlpPure_into_dwlp.
Check DivNonDet.Morphisms.awpPure_into_awp.
Check DivNonDet.Morphisms.awlpPure_into_awlp.
Check DivNonDet.Morphisms.dwpPure_DWP_morphism.
Check DivNonDet.Morphisms.dwlpPure_DWLP_morphism.
Check DivNonDet.Morphisms.awpPure_AWP_morphism.
Check DivNonDet.Morphisms.awlpPure_AWLP_morphism.
Check DivNonDetSt.Morphisms.dwpSt_DWPSt_morphism.
Check DivNonDetSt.Morphisms.dwlpSt_DWLPSt_morphism.
Check DivNonDetSt.Morphisms.awpSt_AWPSt_morphism.
Check DivNonDetSt.Morphisms.awlpSt_AWLPSt_morphism.
Print WPVariants.WPSubStExc.
Check WPVariants.OrderedMonad_WPSubStExc.
Check DivNonDetStExc.Morphisms.dwpStExc_DWPStExc_morphism.
Check DivNonDetStExc.Morphisms.dwlpStExc_DWLPStExc_morphism.
Check DivNonDetStExc.Morphisms.awpStExc_AWPStExc_morphism.
Check DivNonDetStExc.Morphisms.awlpStExc_AWLPStExc_morphism.
Check DivNonDet.Morphisms.dwpPure_DWP_complete.
Check DivNonDet.Morphisms.dwlpPure_DWLP_complete.
Check DivNonDet.Morphisms.awpPure_AWP_complete.
Check DivNonDet.Morphisms.awlpPure_AWLP_complete.
Check DivNonDetSt.Morphisms.dwpSt_DWPSt_complete.
Check DivNonDetSt.Morphisms.dwlpSt_DWLPSt_complete.
Check DivNonDetSt.Morphisms.awpSt_AWPSt_complete.
Check DivNonDetSt.Morphisms.awlpSt_AWLPSt_complete.
Check DivNonDetStExc.Morphisms.dwpStExc_DWPStExc_complete.
Check DivNonDetStExc.Morphisms.dwlpStExc_DWLPStExc_complete.
Check DivNonDetStExc.Morphisms.awpStExc_AWPStExc_complete.
Check DivNonDetStExc.Morphisms.awlpStExc_AWLPStExc_complete.

(* ================================================================= *)
(** ** Section 4.1, Taxonomy of triples                              *)
(* ================================================================= *)

(** Implication, contrapositive and Galois connection between
    transformers, and what each says of triples. *)
Print TransformerRelations.pt_le.
Check TransformerRelations.pt_le_under.
Check TransformerRelations.pt_le_over.
Print TransformerRelations.Contrapositive.
Check TransformerRelations.Contrapositive_under_over.
Check TransformerRelations.Contrapositive_over_under.
Print TransformerRelations.GaloisPT.
Check TransformerRelations.GaloisPT_over_under.


(** Figure 5 of Verscht and Kaminski.

  18~  b ⊆ awp c   =1=>  b ⊆ awlp c <~17~> dwp c ⊆ b   <=2=  dwlp c ⊆ b ~18
           /\                /\                /\                /\
         9 ||             10 ||             11 ||             12 ||
  20~  b ⊆ dwp c   =3=>  b ⊆ dwlp c <~19~> awp c ⊆ b   <=4=  awlp c ⊆ b ~20
                             ^                 ^
                          25 |              26 |
                             v                 v
  22~  aslp b ⊆ c  =5=>  asp b ⊆ c  <~21~> c ⊆ dslp b  <=6=  c ⊆ dsp b  ~22
        13 ||             14 ||             15 ||             16 ||
           \/                \/                \/                \/
  24~  dslp b ⊆ c  =7=>  dsp b ⊆ c  <~23~> c ⊆ aslp b  <=8=  c ⊆ asp b  ~24

    Implications follow the arrowheads: =N=> along a row, || between
    rows.  Contrapositives (negating b and c): <~N~>, and ~N at both ends
    of a row for the arc between its outer triples.  Galois connections
    (iff): 25 and 26.  Some of the logics are named:
      b ⊆ dwp c   TotalCorr      b ⊆ dwlp c   PartCorr
      b ⊆ awp c   LisbonLogic    b ⊆ awlp c   AngPartCorr
      c ⊆ dsp b   DemIncorr      c ⊆ dslp b   PartIncorr
      c ⊆ asp b   IncorrLogic    c ⊆ aslp b   AngPartIncorr *)

(** Implications. *)
Check DivNonDetSt.TriplesTaxonomy.LisbonLogic_impl_AngPartCorr. (* 1 *)
Check DivNonDetSt.TriplesTaxonomy.dwlp_over_impl_dwp_over. (* 2 *)
Check DivNonDetSt.TriplesTaxonomy.TotalCorr_impl_PartCorr. (* 3 *)
Check DivNonDetSt.TriplesTaxonomy.awlp_over_impl_awp_over. (* 4 *)
Check DivNonDetSt.TriplesTaxonomy.aslp_over_impl_asp_over. (* 5 *)
Check DivNonDetSt.TriplesTaxonomy.DemIncorr_impl_PartIncorr. (* 6 *)
Check DivNonDetSt.TriplesTaxonomy.dslp_over_impl_dsp_over. (* 7 *)
Check DivNonDetSt.TriplesTaxonomy.IncorrLogic_impl_AngPartIncorr. (* 8 *)
Check DivNonDetSt.TriplesTaxonomy.TotalCorr_impl_LisbonLogic. (* 9 *)
Check DivNonDetSt.TriplesTaxonomy.PartCorr_impl_AngPartCorr. (* 10 *)
Check DivNonDetSt.TriplesTaxonomy.awp_over_impl_dwp_over. (* 11 *)
Check DivNonDetSt.TriplesTaxonomy.awlp_over_impl_dwlp_over. (* 12 *)
Check DivNonDetSt.TriplesTaxonomy.aslp_over_impl_dslp_over. (* 13 *)
Check DivNonDetSt.TriplesTaxonomy.asp_over_impl_dsp_over. (* 14 *)
Check DivNonDetSt.TriplesTaxonomy.PartIncorr_impl_AngPartIncorr. (* 15 *)
Check DivNonDetSt.TriplesTaxonomy.DemIncorr_impl_IncorrLogic. (* 16 *)
(** Contrapositives. *)
Check DivNonDetSt.TriplesTaxonomy.AngPartCorr_contra_dwp_over. (* 17 *)
Check DivNonDetSt.TriplesTaxonomy.LisbonLogic_contra_dwlp_over. (* 18 *)
Check DivNonDetSt.TriplesTaxonomy.PartCorr_contra_awp_over. (* 19 *)
Check DivNonDetSt.TriplesTaxonomy.TotalCorr_contra_awlp_over. (* 20 *)
Check DivNonDetSt.TriplesTaxonomy.PartIncorr_contra_asp_over. (* 21 *)
Check DivNonDetSt.TriplesTaxonomy.DemIncorr_contra_aslp_over. (* 22 *)
Check DivNonDetSt.TriplesTaxonomy.AngPartIncorr_contra_dsp_over. (* 23 *)
Check DivNonDetSt.TriplesTaxonomy.IncorrLogic_contra_dslp_over. (* 24 *)
(** Galois connections. *)
Check DivNonDetSt.TriplesTaxonomy.PartCorr_galois_asp_over. (* 25 *)
Check DivNonDetSt.TriplesTaxonomy.awp_over_galois_PartIncorr. (* 26 *)

(* ================================================================= *)
(** ** Section 4.2, Monadic relations (Figure 1)                     *)
(* ================================================================= *)

(** Figure 1, with its edges numbered.  The numbers are shared by the two
    diagrams; the check stating an edge carries its number, prefixed [a]
    for diagram (a) and [b] for diagram (b).

    (a) Base monads                     (b) Monads with state

            ASLP                                ASLP
       1 ⇗   :                            1∗ ⇗   :   ⇖ 2⋆
        ⇗    :9    ≅ 2                      ⇗    :9   ⇖
     ASP <~~ 10 ~~> DSLP                 ASP <~~ 10 ~~> DSLP
     |       :     ⇗ ^                   | ⇖     :     ⇗ ^
     |  ≅ 3  :  4⇗   |                   |  ⇖ 3∗ : 4⋆ ⇗  |
     |       : ⇗     |                   |   ⇖   :   ⇗   |
  13 |      DSP      | 14             13 |      DSP      | 14
     |               |                   |               |
     |     AWLP      |                   |     AWLP      |
     | 5 ⇗   :   ⇖ 6 |                   | 5 ⇗   :   ⇖ 6 |
     v  ⇗    :11  ⇖  |                   v  ⇗    :11  ⇖  |
     DWLP <~ 12 ~> AWP                   DWLP <~ 12 ~> AWP
        ⇖    :    ⇗                         ⇖    :    ⇗
       7 ⇖   :   ⇗ 8                       7 ⇖   :   ⇗ 8
            DWP                                 DWP

    Implications, pointing up (toward ASLP and AWLP):
      1 ASP => ASLP    2 DSLP => ASLP   3 DSP => ASP     4 DSP => DSLP
      5 DWLP => AWLP   6 AWP => AWLP    7 DWP => DWLP    8 DWP => AWP
    Isomorphisms, in (a), in place of 2 and 3:
      2 ASLP ≅ DSLP    3 ASP ≅ DSP
    Contrapositives:
      9 ASLP -- DSP   10 ASP -- DSLP   11 AWLP -- DWP   12 DWLP -- AWP
    Galois connections, from the left adjoint:
     13 ASP -> DWLP   14 AWP -> DSLP
    [∗] and [⋆]: through the [aspOf], respectively [dslpOf], component.
    An implication X => Y is [MonadRelation_x_implies_y]: [X ⊑ Y]. *)

(** DM4all's monadic relation. *)
Print MonadRelation.MonadRelation.

(** Figure 1(a), base monads.  The wp edges are generic in the two
    conditions; DSP collapses into ASP and ASLP into DSLP.  The sp
    implications relate the elements themselves: every ASP element implies
    every ASLP element, and every DSP element every DSLP element. *)
Check MonadTaxonomy.MonadRelation_asp_implies_aslp_pure. (* a1 *)
Check MonadTaxonomy.asp_implies_aslp_any_pure.
Check MonadTaxonomy.MonadRelation_aslp_dslp_pure. (* a2 *)
Check MonadTaxonomy.MonadRelation_dsp_asp_pure. (* a3 *)
Check MonadTaxonomy.MonadRelation_dsp_implies_dslp_pure. (* a4 *)
Check MonadTaxonomy.dsp_implies_dslp_any_pure.
Check MonadTaxonomy.MonadRelation_implies_toWPure. (* a5-a8 *)
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_pure. (* a9 *)
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_pure. (* a10 *)
Check MonadTaxonomy.MonadRelation_contra_toWPure. (* a11-a12 *)
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp_pure. (* a13 *)
Check MonadTaxonomy.MonadRelation_galois_awp_dslp_pure. (* a14 *)

(** Figure 1(b), monads with state. *)

(** The four stateful sp monads share [SPSt] and its order;
    [⊑] is not a monadic relation between DSP / ASLP and ASP / DSLP, as
    their binds are not monotone (Figure 2). *)
Print MonotoneSPSt.SPStMonotone.SPStMon.
Print MonadTaxonomy.impliesSPSt.
Check ASLPMonad.aslp_arbitrary_bind_impossible.
Check DSPMonad.dsp_arbitrary_bind_impossible.

(** Figure 1(b) sp implication edges: the DSP and ASLP binds
    are computed through their components, the relations through the
    components are monadic, and each entails [⊑] of the sps themselves
    (the asterisks). *)
Check SPStBindComparisons.bindASLPSt_SPStMonotone.
Check SPStBindComparisons.bindDSPSt_SPStMonotone.
Check MonadTaxonomy.MonadRelation_asp_implies_aslp. (* b1 *)
Check MonadTaxonomy.asp_implies_aslp_part.
Check MonadTaxonomy.MonadRelation_dslp_implies_aslp. (* b2 *)
Check MonadTaxonomy.dslp_implies_aslp_part.
Check MonadTaxonomy.MonadRelation_dsp_implies_asp. (* b3 *)
Check MonadTaxonomy.dsp_implies_asp_part.
Check MonadTaxonomy.MonadRelation_dsp_implies_dslp. (* b4 *)
Check MonadTaxonomy.dsp_implies_dslp_part.

(** The stateful wp monads are submonads of [WSt]; the order
    [⊑] on [WSt] is a monadic relation between any two of them. *)
Check WPVariants.toWSt_ret.
Check WPVariants.toWSt_bind.
Print MonadTaxonomy.impliesWSt.
Check MonadTaxonomy.MonadRelation_implies_toWSt.
Check MonadTaxonomy.MonadRelation_impliesWSt.

(** What [⊑] between wps says of their triples. *)
Check TransformerRelations.pt_le_under.
Check TransformerRelations.pt_le_over.

(** Figure 1(b), wp implication edges (each also with its converse). *)
Check MonadTaxonomy.MonadRelation_dwlp_implies_awlp. (* b5 *)
Check MonadTaxonomy.MonadRelation_awlp_implies_dwlp.
Check MonadTaxonomy.MonadRelation_awp_implies_awlp. (* b6 *)
Check MonadTaxonomy.MonadRelation_awlp_implies_awp.
Check MonadTaxonomy.MonadRelation_dwp_implies_dwlp. (* b7 *)
Check MonadTaxonomy.MonadRelation_dwlp_implies_dwp.
Check MonadTaxonomy.MonadRelation_dwp_implies_awp. (* b8 *)
Check MonadTaxonomy.MonadRelation_awp_implies_dwp.

(** Figure 1(b) sp contrapositive edges: [⋈] on [SPSt] is
    monadic between DSP and ASLP, ASP and DSLP, one to one, swapping the
    components and meets with joins; symmetric. *)
Print MonadTaxonomy.contraSPSt.
Check MonadTaxonomy.MonadRelation_contraSPSt.
Check MonadTaxonomy.contraSPSt_meet_join.
Check MonadTaxonomy.contraSPSt_join_meet.
Check MonadTaxonomy.contraSPSt_sym.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_one. (* b9 *)
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_two. (* b9 *)
Check MonadTaxonomy.contra_dsp_in_aslp.
Check MonadTaxonomy.contra_aslp_in_dsp.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_one. (* b10 *)
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_two. (* b10 *)
Check MonadTaxonomy.contra_asp_in_dslp.
Check MonadTaxonomy.contra_dslp_in_asp.

(** Figure 1(b) wp contrapositive edges: [⋈] on [WSt] is
    monadic between DWP and AWLP, AWP and DWLP, one to one, and
    symmetric. *)
Print MonadTaxonomy.contraWSt.
Check MonadTaxonomy.MonadRelation_contraWSt.
Check MonadTaxonomy.contraWSt_sym.
Check MonadTaxonomy.MonadRelation_contra_dwp_awlp_one. (* b11 *)
Check MonadTaxonomy.MonadRelation_contra_dwp_awlp_two. (* b11 *)
Check MonadTaxonomy.contra_dwp_in_awlp.
Check MonadTaxonomy.contra_awlp_in_dwp.
Check MonadTaxonomy.MonadRelation_contra_awp_dwlp_one. (* b12 *)
Check MonadTaxonomy.MonadRelation_contra_awp_dwlp_two. (* b12 *)
Check MonadTaxonomy.contra_awp_in_dwlp.
Check MonadTaxonomy.contra_dwlp_in_awp.

(** Figure 1(b) Galois edge ASP -> DWLP: [Ladj] is a monadic
    relation (angelic structure), its sps are disjunctive and strict and its
    wps conjunctive and terminating, it restricts to ASP and DWLP, one to
    one. *)
Print MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj.
Print MonadTaxonomy.GaloisSPWP.
Check MonadTaxonomy.Ladj_GaloisSPWP.
Check MonadTaxonomy.MonadRelation_GaloisSPWP.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_colim.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_lim.
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp. (* b13 *)
Check MonadTaxonomy.galois_asp_in_dwlp.
Check MonadTaxonomy.galois_dwlp_in_asp.

(** Figure 1(b) Galois edge AWP -> DSLP: [Radj], demonic
    structure, restricts to AWP and DSLP, one to one. *)
Print MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj.
Print MonadTaxonomy.GaloisWPSP.
Check MonadTaxonomy.Radj_GaloisWPSP.
Check MonadTaxonomy.MonadRelation_GaloisWPSP.
Check MonadTaxonomy.MonadRelation_galois_awp_dslp. (* b14 *)
Check MonadTaxonomy.galois_awp_in_dslp.
Check MonadTaxonomy.galois_dslp_in_awp.

(** Contrapositive pairs exchange [Ladj] and [Radj]. *)
Check MonadTaxonomy.Ladj_iff_Radj.

(* ================================================================= *)
(** ** Section 4.3, Base case collapse                               *)
(* ================================================================= *)

(** Without state, DSP and ASP (ASLP and DSLP) have the same
    elements, [ret] and [bind]: the identity is an isomorphism of ordered
    monads. *)
Check DSPMonad.dsp_to_asp_morphism.
Check DSPMonad.asp_to_dsp_morphism.
Check DSPMonad.asp_to_dsp_to_asp.
Check DSPMonad.dsp_to_asp_to_dsp.
Check DSPMonad.OrderedMonad_DSP.
Check ASLPMonad.aslp_to_dslp_morphism.
Check ASLPMonad.dslp_to_aslp_morphism.
Check ASLPMonad.dslp_to_aslp_to_dslp.
Check ASLPMonad.aslp_to_dslp_to_aslp.
Check ASLPMonad.OrderedMonad_ASLP.

(** With state, a result reachable from two initial states
    tells them apart. *)
Check DSPASLPArr.no_ASPArr_for_dsp.
Check DSPASLPArr.no_DSLPArr_for_aslp.

(* ================================================================= *)
(** ** Section 5, Specifying monadic programs                        *)
(* ================================================================= *)

(** Monad morphisms; triples of a monad morphism, under and
    over; specification of a computation by an element; specification
    monads. *)
Print OrderedMonad.MonadMorphism.
Print Generic.Triple.triple.
Print Generic.Triple.pt_holds.
Print Generic.Triple.Under.
Print Generic.Triple.Over.

(** The stateful computation monad and the eight stateful
    morphisms, with their readings on outcomes. *)
Print DivNonDetSt.Computation.stdivndNE.
Print DivNonDetSt.Computation.outSt.
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
Print RelSPostArr.dspOf.
Print RelSPostArr.aslpOf.

(** The base wp morphisms, lifted by [stateT] to the stateful
    ones. *)
Check DivNonDet.Morphisms.dwpPure_morphism.
Check DivNonDet.Morphisms.dwlpPure_morphism.
Check DivNonDet.Morphisms.awpPure_morphism.
Check DivNonDet.Morphisms.awlpPure_morphism.
Check Monad.TransformerLaws.MonadMorphism_stateT.
Check DivNonDetSt.Morphisms.wpSt_morphism.

(** Arrow morphisms into the four base sp arrows,
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

(** sp triples; each edge of Figure 1(b) relates the
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

(** The running program on even and odd states, its AWP and
    ASP transformers; Lisbon logic fails (at [s = 1]) where incorrectness
    logic holds; with [p'] both hold. *)
Print ResetEven.m.
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

(** Composition (Section 5.3): two triples and an intermediate
    assertion give one for the sequenced computation.  The rule holds by
    monotonicity and the monad morphism law, and the over-approximate one
    flips the three orderings and the side condition, so all eight kinds
    of wp triples compose.  The asp and dslp rules hold in both
    directions, reversing the wp rules' side conditions; the
    under-approximate asp rule and the over-approximate dslp rule
    additionally require the result type to be inhabited.  An
    under-approximate dsp triple is the conjunction of an asp and a dslp
    triple, and so is an over-approximate aslp triple, so these compose
    through their components.  The two remaining kinds do not compose,
    witnessed by the programs of Figure 2. *)
Check Generic.Triple.seq_side.
Check Generic.Triple.pt_holds_backward_seq.
Check DivNonDetSt.Triples.wpSt_bind_read.
Check DivNonDetSt.Triples.spec_holds_wpSt_seq.
Check DivNonDetSt.Triples.triple_dwpSt_seq.
Check DivNonDetSt.Triples.triple_dwlpSt_seq.
Check DivNonDetSt.Triples.triple_awpSt_seq.
Check DivNonDetSt.Triples.triple_awlpSt_seq.
Check Generic.Triple.seq_side_fwd.
Check Generic.Triple.pt_holds_forward_join_under_seq.
Check Generic.Triple.pt_holds_forward_join_over_seq.
Check Generic.Triple.pt_holds_forward_meet_under_seq.
Check Generic.Triple.pt_holds_forward_meet_over_seq.
Check Generic.Triple.forward_join_under_seq_needs_inhabited.
Check Generic.Triple.forward_meet_over_seq_needs_inhabited.
Check DivNonDetSt.Triples.aspSt_bind_read.
Check DivNonDetSt.Triples.dslpSt_bind_read.
Check DivNonDetSt.Triples.triple_aspSt_seq_under.
Check DivNonDetSt.Triples.triple_aspSt_seq_over.
Check DivNonDetSt.Triples.triple_dslpSt_seq_under.
Check DivNonDetSt.Triples.triple_dslpSt_seq_over.
Check DivNonDetSt.Triples.triple_dspSt_split_under.
Check DivNonDetSt.Triples.triple_aslpSt_split_over.
Check DivNonDetSt.Triples.triple_dspSt_seq_under.
Check DivNonDetSt.Triples.triple_aslpSt_seq_over.
Print DivNonDetSt.Triples.seqFst.
Print DivNonDetSt.Triples.seqSnd.
Check DivNonDetSt.Triples.seqSeq_out_some.
Check DivNonDetSt.Triples.dspSt_seq_over_fails.
Check DivNonDetSt.Triples.aslpSt_seq_under_fails.

(** The comparison rule is the bind typing of the Dijkstra
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

(** The AWP specification of the running program, its
    comparison (a Dijkstra-monad typing), and its equivalence with the
    pre/post pair. *)
Print ResetEven.wspec.
Check ResetEven.awp_m_le_wspec.
Print ResetEven.m_DM.
Check ResetEven.wspec_pp2wp.
Check ResetEven.le_wspec_iff_lisbon.

(** wp triples, ASP over and DSLP under triples embed as
    specifications ([pp2wp_under], [pp2wp_over], [pp2asp_over],
    [pp2dslp_under]). *)
Print DivNonDetSt.Typings.wpUnderSt.
Print DivNonDetSt.Typings.wpOverSt.
Check DivNonDetSt.Typings.triple_under_wpSt.
Check DivNonDetSt.Typings.triple_over_wpSt.
Print Generic.Typings.aspOver.
Print Generic.Typings.dslpUnder.
Check Generic.Typings.le_aspOver.
Check Generic.Typings.le_dslpUnder.
Check DivNonDetSt.Typings.triple_over_aspSt.
Check DivNonDetSt.Typings.triple_under_dslpSt.

(** No specification embeds ASP under (nor DSLP over)
    triples; an ASP specification may still match a triple, but typing at
    it is strictly stronger than the triple. *)
Check DivNonDetSt.Typings.no_asp_under_index.
Check DivNonDetSt.Typings.no_dslp_over_index.
Check Generic.Typings.le_aspUnder.
Check Generic.Typings.aspUnder_typing_triple.
Check DijkstraExamples.progA_Dasp_op.
Check DijkstraExamples.progloom_harder_not_Dasp_op.

(** The Dijkstra monad of a monad morphism, its operations
    and DM4all's laws; also with the order flipped. *)
Print DijkstraMonad.OrderedTarget.
Print DijkstraMonad.DM.
Print DijkstraMonad.DM_ret.
Print DijkstraMonad.DM_bind.
Print DijkstraMonad.DM_wkn.
Print DijkstraMonad.DijkstraLaws.
Check DijkstraMonad.DM_laws.
Print DijkstraMonad.DMop.
Check DijkstraMonad.DMop_laws.

(** Dijkstra monads for the four wp monads, ASP and DSLP
    (with state; with exceptions, with their laws).  The verified examples
    are elements of them: the typings above are biconditional, so a triple
    of an embeddable kind is already the specification its computation
    types at, and [m_DM] works that out for the Lisbon triple of the
    running program. *)
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
Check ResetEven.wspec.
Check ResetEven.le_wspec_iff_lisbon.
Check ResetEven.m_DM.
Check DijkstraExamples.progA_Ddwp.
Check DijkstraExamples.progB_Ddwlp.
Check DijkstraExamples.progA_Dawp.
Check DijkstraExamples.progB_Dawlp.
Check DijkstraExamples.progA_Dasp.
Check DijkstraExamples.progEx_Ddslp_op.

(* ================================================================= *)
(** ** Section 6, Galois connections between specification monads    *)
(* ================================================================= *)

(** DM4all's Galois connections between [Pred], [PrePost] and
    [WP] (diagram); [Pred] is a specification monad. *)
Check PredMonad.OrderedMonad_Pred.
Check BaseGaloisConnections.pred_pp_adjunction.
Check BaseGaloisConnections.wp_pp_under_adjunction.
Check BaseGaloisConnections.wp_pp_over_adjunction.

(** The [SPost] -- [Pred] edge of the diagram. *)
Print GaloisArr.Galois_Rel_SPost.

(** Monotone monad transformers preserve Galois connections. *)
Check MonadRelation.MonadRelation_stateT.
Check MonadRelation.MonadRelation_optionT.

(** The stateful [Pred]; [φ] and [ψ] are monad morphisms
    (angelic structure); [Ladj (φ p) (ψ p)], and every [Ladj] pair is of
    this form; [φ ⊣ φ'] and [φ'] preserves the angelic structure;
    [ψ ⊣ ψ'], and [ψ'] does not preserve WP's [bind];
    the maps are monotone; the adjoints are colimit/limit preserving; ASP is
    isomorphic to DWLP. *)
Print PredMonad.PredSt.PredSt.
Print PredMonad.PredSt.ordPredSt.
Print MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred.
Print MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_ret.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_bind.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_ret.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_bind.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_fromPred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.Ladj_pred.
Print MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fromPred_toPred_adj.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_ret.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.toPred_bind.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_monotone.
Print MonotoneSPSt.SPStMonotone.AngelicMonotone.WSt2pred.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.WSt2pred_monotone.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.pred2WSt_Wst2pred_adj.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.WSt2pred_bind_counterexample.
Check MonadTaxonomy.galois_asp_dwlp_order.
Check SPostArrEquiv.asp_to_rel_morphism.

(** The demonic side: [ξ] (monotone into [Pred^op]), [ζ],
    [ξ'], [ζ']; [ξ' ⊣ ξ], [ζ ⊣ ζ'], and [ζ'] does not preserve WP's
    [bind]; [ξ] and [ζ] are monad morphisms (demonic structure);
    the lax demonic bind (footnote); [Radj (ξ p) (ζ p)], and every [Radj]
    pair is of this form; nuclei and limits; DSLP is isomorphic to AWP. *)
Print MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_antitone.
Print MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_antitone.
Print MonotoneSPSt.SPStMonotone.DemonicMonotone.WSt2pred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.WSt2pred_antitone.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_Wst2pred_adj.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.WSt2pred_bind_counterexample.
Print MonotoneSPSt.SPStMonotone.DemonicMonotone.toPred.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_toPred_adj.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_ret.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fromPred_bind.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_ret.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.pred2WSt_bind.
Print MonotoneSPSt.SPStMonotone.DemonicMonotone.bindP.
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

(** The nuclei of the four adjunctions, and the two chains they give.
    (1) every stateful predicate is a fixed point of both round trips
    through the sp and the wp side; (2) and (3) the fixed points of the
    other two round trips are exactly the elements of ASP and DWLP
    (angelic), DSLP and AWP (demonic).  "Exactly" is both directions: the
    carrier conditions the nuclei are stated against hold of every element
    of the named monad, and a transformer satisfying one is such an
    element, recovered unchanged. *)
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.tPfP_unit.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.tPfP_unit_inv.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.tPfP_Wst_unit.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.tPfP_Wst_unit_inv.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_unit.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_unit_inv.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_fix_disj_strict.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_Wst_unit.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_Wst_unit_inv.
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.fPtP_Wst_fix_conj_term.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.tPfP_Wst_unit.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.tPfP_Wst_unit_inv.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_fix_conj_term.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_Wst_unit.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_Wst_unit_inv.
Check MonotoneSPSt.SPStMonotone.DemonicMonotone.fPtP_Wst_fix_disj_strict.
Check MonadTaxonomy.asp_disj_strict.
Check MonadTaxonomy.dslp_conj_term.
Check MonadTaxonomy.dwlp_conj_term.
Check MonadTaxonomy.awp_disj_strict.
Check MonadTaxonomy.sp_disj_strict_is_asp.
Check MonadTaxonomy.sp_conj_term_is_dslp.
Check MonadTaxonomy.wp_conj_term_is_dwlp.
Check MonadTaxonomy.wp_disj_strict_is_awp.

(* ================================================================= *)
(** ** Section 7, Formalization in Rocq                              *)
(* ================================================================= *)

(** Example programs that together use all sixteen kinds of
    triples ([Verification/DivNonDetStExc/TriplesExamples.v]), including
    O'Hearn's sequential examples
    ([Verification/DivNonDetSt/TriplesExamples/IncorrectnessLogic.v]). *)

(** Programs written as interaction trees, mapped into the
    computation monad by a monad morphism. *)
Check DivNonDet.Computation.denote_morphism.
Check DivNonDetSt.Computation.denoteSt_morphism.
Check DivNonDetStExc.Computation.denoteStExc_morphism.

(** Not checkable here: "about 28k lines", "only funext,
    propext and excluded middle" (the build has about 38.6k lines;
    [Checks/Assumptions.v] reports the axioms, which also include
    [eq_rect_eq] -- introduced locally by applying [DivVis] in
    [any_infinite_bind_leaf], not inherited from ITree or paco, whose
    lemmas it calls are closed, and derivable from propositional
    extensionality by [ITreeFacts.eq_rect_eq_from_propext], so the
    paper's three are complete). *)

(* ================================================================= *)
(** ** Appendix A, Arrow laws                                        *)
(* ================================================================= *)

(** The twelve laws, with logical equivalence of sp arrows as
    the equality. *)
Print Arrow.ArrowLaws.
Print Arrow.ArrowApplyLaws.
Print SPostArr.ASPArr_eq.
Print SPostArr.DSLPArr_eq.
Print DSPASLPArr.DSPArr_eq.
Print DSPASLPArr.ASLPArr_eq.

(** The state and option arrow transformers satisfy the arrow
    transformer laws. *)
Check StateArrowT.Core.ArrowLaws_stateArrT.
Check StateArrowT.ArrowApplyLaws.ArrowApplyLaws_stateArrT.
Check OptionArrowT.ArrowLaws.ArrowLaws_optionArrT.
Check OptionArrowT.ArrowApplyLaws.ArrowApplyLaws_optionArrT.

(** All sp arrows are choice arrows, with Hughes's laws and
    Paterson's distribution law; the transformers preserve them. *)
Print Arrow.ArrowChoiceLaws.
Check SPostArr.ArrowChoiceLaws_ASPArr.
Check SPostArr.ArrowChoiceLaws_DSLPArr.
Check DSPASLPArr.ArrowChoiceLaws_DSPArr.
Check DSPASLPArr.ArrowChoiceLaws_ASLPArr.
Check StateArrowT.ArrowChoiceLaws.ArrowChoiceLaws_stateArrT.
Check OptionArrowT.ArrowChoiceLaws.ArrowChoiceLaws_optionArrT.

(* ================================================================= *)
(** ** Appendix B, The DSP and ASLP arrows                           *)
(* ================================================================= *)

(** The two arrows, their parts, operations and laws; direct
    composition of dsps fails; at input [unit] they give DSP and ASLP. *)
Print DSPASLPArr.DSPArr.
Print DSPASLPArr.pure_DSP.
Print DSPASLPArr.comp_DSP.
Print DSPASLPArr.first_DSP.
Print DSPASLPArr.app_DSP.
Check DSPASLPArr.ArrowLaws_DSPArr.
Check DSPASLPArr.ArrowApplyLaws_DSPArr.
Check SPostArrInfrastructure.dsp_naive_transformer_comp_rejects.
Print DSPASLPArr.ASLPArr.
Print DSPASLPArr.pure_ASLP.
Print DSPASLPArr.comp_ASLP.
Print DSPASLPArr.first_ASLP.
Print DSPASLPArr.app_ASLP.
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

(** Lemma lem:asp-singleton; fixing the input of [ASPArr]
    gives the carrier and the [ret] and [bind] of [ASP]. *)
Check ASPMonad.getASP_singleton.
Check ASPMonad.join_iff_singleton.
Check ASPMonad.getASP_ret.
Check ASPMonad.getASP_bind.
Check ASPMonad.aspsp_to_asp_morphism.

(** Dually Lemma lem:dslp-singleton, and the [ret] and [bind]
    of [DSLP]. *)
Check DSLPMonad.getDSLP_msingleton.
Check DSLPMonad.meet_iff_msingleton.
Check DSLPMonad.getDSLP_ret.
Check DSLPMonad.getDSLP_bind.
Check DSLPMonad.dslpsp_to_dslp_morphism.

(* ================================================================= *)
(** ** Appendix D, Stateful sp arrows and monads                     *)
(* ================================================================= *)

(** The [ret] and [bind] of [DSPSt] and [ASLPSt] are computed through
    their [aspOf] and [dslpOf] components. *)
Check DSPMonad.getDSPSt_rel.
Check DSPMonad.dspRelSt_bind_of.
Check ASLPMonad.getASLPSt_rel.
Check ASLPMonad.aslpRelSt_bind_of.

(* ================================================================= *)
(** ** Appendix E, Counterexamples to the monad and arrow laws       *)
(* ================================================================= *)

(** E.1: [SPost_ang(S, A)] (monotone, strict) with the (ang-st) operations:
    the unit laws hold, associativity fails, with the paper's [m], [f], [g]. *)
Print StatefulSPostCounterexample.St.SPostSt.
Check StatefulSPostCounterexample.St.SPostSt_bind_ret_r.
Check StatefulSPostCounterexample.St.SPostSt_bind_ret_l.
Check StatefulSPostCounterexample.St.FailingBind.SPostSt_bind_bind_fails.

(** E.2: [SPost_dem(S, A)] (monotone, terminating) with the (dem-st)
    operations: the unit laws hold, associativity fails, with the paper's
    [m], [f], [g]. *)
Print StatefulSPostCounterexample.Dem.SPostDem.
Check StatefulSPostCounterexample.Dem.SPostDem_bind_ret_r.
Check StatefulSPostCounterexample.Dem.SPostDem_bind_ret_l.
Check StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails.

(** E.3: the monotone, strict sp arrows with the operations of
    [ASPArr] (the codomain condition amounts to strictness) fail
    [first f >>> arr fst = arr fst >>> f], with the paper's [g] and [pre];
    dually for the monotone, terminating arrows with those of [DSLPArr]. *)
Print LawCounterexamples.AngArr.SPArrAng.
Check LawCounterexamples.AngArr.codomain_iff_strict.
Check LawCounterexamples.AngArr.compAng_ASP.
Check LawCounterexamples.AngArr.first_fst_fails.
Check LawCounterexamples.AngArr.not_ArrowLaws.
Print LawCounterexamples.DemArr.SPArrDem.
Check LawCounterexamples.DemArr.codomain_iff_terminating.
Check LawCounterexamples.DemArr.compDem_DSLP.
Check LawCounterexamples.DemArr.first_fst_fails.
Check LawCounterexamples.DemArr.not_ArrowLaws.

(* ================================================================= *)
(** ** Appendix F, Decomposing dsp and aslp predicate transformers   *)
(* ================================================================= *)

(** Lemmas lem:dsp-split and lem:aslp-split, and the health
    of the components. *)
Check DSPASLPArr.dsp_split.
Print DSPASLPArr.aspPartArr.
Print DSPASLPArr.dslpPartArr.
Check DSPASLPArr.aslp_split.
Print DSPASLPArr.aspPartAArr.
Print DSPASLPArr.dslpPartAArr.

(* ================================================================= *)
(** ** Appendix G, Monadic relations between the base monads         *)
(* ================================================================= *)

(** The relations of Figure 1(a) (checked in Section 4.2); [Ladj]
    and [Radj] are proved between [WPure] and [Pred]. *)
Check MonadTaxonomy.MonadRelation_GaloisPredWP.
Check MonadTaxonomy.MonadRelation_GaloisWPPred.
