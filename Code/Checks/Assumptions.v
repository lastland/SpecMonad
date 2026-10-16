(** Console assumption reports, compiled explicitly by [make check].
    Do not import test or regression modules or report test or regression
    declarations, including regression lemmas colocated with production code. *)
From Incorrectness.Lib.Arrow Require Import
  Arrow ArrowApplyFacts ArrowMonad OptionArrowT StateArrowT RelArrowCoherence.
From Incorrectness.SP Require Import
  SPostArr DSPASLPArr.
From Incorrectness.Relational Require Import
  RelSPostArr Rel.
From Incorrectness.SP Require Import
  SPostArrEquiv.
From Incorrectness.PTMonadTaxonomy Require Import
  TransformerRelations.
From Incorrectness.GaloisConnections Require Import
  GaloisArr PrePostArr RelPrePostArr WPArr.
From Incorrectness.SP Require
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.GaloisConnections Require
  BaseGaloisConnections.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.

(** Core laws now supply pointwise pure congruence. The lift helper still
    takes source congruence independently of target core laws. Option law
    packages use the selected base field; state core laws retain their existing
    extensionality uses. These reports are conditional on their dictionaries. *)
Print Assumptions Arrow.pure_proper.
Print Assumptions Arrow.lift_pure_proper.
Print Assumptions Arrow.first_constant.
Print Assumptions Arrow.pure_comp_ext.
Print Assumptions ArrowApplyFacts.app_constant.
Print Assumptions ArrowMonad.MonadLawsE_Arrow.
Print Assumptions ArrowLaws_optionArrT.
Print Assumptions ArrowChoiceLaws_optionArrT.
Print Assumptions ArrowApplyLaws_optionArrT.
Print Assumptions ArrowLaws_stateArrT.
Print Assumptions ArrowChoiceLaws_stateArrT.
Print Assumptions ArrowApplyLaws_stateArrT.
Print Assumptions RelArrowCoherence.rel_arrow_laws.
Print Assumptions RelArrowCoherence.rel_arrow_laws_leibniz.
Print Assumptions PrePostArr.ArrowLaws_PrePost.
Print Assumptions RelPrePostArr.ArrowLaws_RelPrePost.
Print Assumptions WPArr.ArrowLaws_WPArr.

(** Computation-owned outcome laws use pointwise equivalence and are
    closed under the global context. Colocated empty-prefix regressions
    remain outside this audit. *)
Print Assumptions Computation.outcomes_bind.
Print Assumptions Computation.diverge_absorbing.
Print Assumptions Computation.outSt_bind.
Print Assumptions Computation.outStExc_bind.

(** Shared structural equations: each uses only its explicit relational
    hypotheses, including faithfulness, with no global axioms. *)
Print Assumptions RelArrowCoherence.rel_comp_id_l_fields.
Print Assumptions RelArrowCoherence.rel_comp_id_r_fields.
Print Assumptions RelArrowCoherence.rel_comp_assoc_fields.
Print Assumptions RelArrowCoherence.rel_pure_comp_fields.
Print Assumptions RelArrowCoherence.rel_first_pure_fields.
Print Assumptions RelArrowCoherence.rel_first_comp_fields.
Print Assumptions RelArrowCoherence.rel_first_fst_fields.
Print Assumptions RelArrowCoherence.rel_first_assoc_fields.
Print Assumptions RelArrowCoherence.rel_first_natural_fields.
Print Assumptions RelArrowCoherence.rel_left_pure_fields.
Print Assumptions RelArrowCoherence.rel_left_comp_fields.
Print Assumptions RelArrowCoherence.rel_left_inl_fields.
Print Assumptions RelArrowCoherence.rel_left_assoc_fields.
Print Assumptions RelArrowCoherence.rel_left_inr_fields.
Print Assumptions RelArrowCoherence.rel_left_natural_fields.
Print Assumptions RelArrowCoherence.rel_first_left_dist_fields.

(** Concrete law packages for property-only SP arrows and the shared
    relational carrier. *)
Print Assumptions SPostArr.ArrowLaws_PureASPostArr.
Print Assumptions SPostArr.ArrowChoiceLaws_PureASPostArr.
Print Assumptions SPostArr.ArrowApplyLaws_PureASPostArr.
Print Assumptions SPostArr.ArrowLaws_PureDSLPostArr.
Print Assumptions SPostArr.ArrowChoiceLaws_PureDSLPostArr.
Print Assumptions SPostArr.ArrowApplyLaws_PureDSLPostArr.
Print Assumptions Rel.ArrowLaws_Rel.
Print Assumptions Rel.ArrowChoiceLaws_Rel.
Print Assumptions Rel.ArrowApplyLaws_Rel.

(** Direct-Rel round trips and semantic morphisms, including higher-order
    application and state-over-option lifts. *)
Print Assumptions ArrowMorphism.inverse_morphism.
Print Assumptions ArrowMorphism.option_arrow_morphism.
Print Assumptions ArrowMorphism.state_arrow_morphism.
Print Assumptions ArrowMorphism.state_option_arrow_morphism.
Print Assumptions SPostArrEquiv.asp_from_to.
Print Assumptions SPostArrEquiv.asp_to_from.
Print Assumptions SPostArrEquiv.dslp_from_to.
Print Assumptions SPostArrEquiv.dslp_to_from.
Print Assumptions SPostArrEquiv.option_asp_to_from.
Print Assumptions SPostArrEquiv.option_dslp_to_from.
Print Assumptions SPostArrEquiv.state_option_asp_to_from.
Print Assumptions SPostArrEquiv.state_option_dslp_to_from.
Print Assumptions SPostArrEquiv.asp_to_rel_morphism.
Print Assumptions SPostArrEquiv.asp_from_rel_morphism.
Print Assumptions SPostArrEquiv.dslp_to_rel_morphism.
Print Assumptions SPostArrEquiv.dslp_from_rel_morphism.
Print Assumptions SPostArrEquiv.state_option_asp_to_rel_morphism.
Print Assumptions SPostArrEquiv.state_option_asp_from_rel_morphism.
Print Assumptions SPostArrEquiv.state_option_dslp_to_rel_morphism.
Print Assumptions SPostArrEquiv.state_option_dslp_from_rel_morphism.
Print Assumptions SPostArrEquiv.optionASP_no_lawful_ArrowLoop.
Print Assumptions SPostArrEquiv.optionDSLP_no_lawful_ArrowLoop.

(** Generic coherence: axiom-free. *)
Print Assumptions RelArrowCoherence.rel_state_option_bind_fields.
Print Assumptions RelArrowCoherence.rel_state_option_bind.

(** The adjunction is axiom-free.  The second WP/PrePost adjunction uses
    excluded middle. *)
Print Assumptions GaloisArr.adjunction_RPP_WP.
Print Assumptions GaloisArr.Galois_RPP_WP.
Print Assumptions BaseGaloisConnections.wp_pp_over_adjunction.

(** DSP and ASLP under their pointwise order.  With state and with
    exceptions the monad is not ordered: excluded middle, through the
    recovered relation.  No bind at all is left-unital and monotone: closed
    for DSP; the ASLP statement mentions the ASLP return, whose carrier
    proof uses excluded middle.  Without state both are ordered, as ASP and
    DSLP: excluded middle. *)
Print Assumptions DSPMonad.not_OrderedMonad_DSPSt.
Print Assumptions ASLPMonad.not_OrderedMonad_ASLPSt.
Print Assumptions DSPMonad.not_OrderedMonad_DSPStExc.
Print Assumptions ASLPMonad.not_OrderedMonad_ASLPStExc.
Print Assumptions DSPMonad.dsp_arbitrary_bind_impossible.
Print Assumptions ASLPMonad.aslp_arbitrary_bind_impossible.
Print Assumptions DSPMonad.OrderedMonad_DSP.
Print Assumptions ASLPMonad.OrderedMonad_ASLP.

(** The directly defined stateless monads are the arrow-derived ones: both
    maps are monad morphisms.  Closed for ASP; excluded middle for DSLP; DSP
    and ASLP add propositional extensionality, through the equivalence of
    their carrier condition with ASP's and DSLP's. *)
Print Assumptions ASPMonad.aspsp_to_asp_morphism.
Print Assumptions ASPMonad.asp_to_aspsp_morphism.
Print Assumptions ASPMonad.OrderedMonad_ASPSP.
Print Assumptions DSLPMonad.dslpsp_to_dslp_morphism.
Print Assumptions DSLPMonad.dslp_to_dslpsp_morphism.
Print Assumptions DSLPMonad.OrderedMonad_DSLPSP.
Print Assumptions DSPMonad.dspsp_to_dsp_morphism.
Print Assumptions DSPMonad.dsp_to_dspsp_morphism.
Print Assumptions DSPMonad.OrderedMonad_DSPSP.
Print Assumptions ASLPMonad.aslpsp_to_aslp_morphism.
Print Assumptions ASLPMonad.aslp_to_aslpsp_morphism.
Print Assumptions ASLPMonad.OrderedMonad_ASLPSP.
Print Assumptions TransformerLaws.bind_optionT_mono.

(** Maillard's existential monad and the local universal dual are equivalent
    to healthy ASP and DSLP arrows, respectively, at input [unit], up to
    pointwise logical equivalence. All original/ASP reports below, including
    the top counterexample, are closed. The demonic monad laws, healthiness,
    round trips, both morphisms, and forward order comparison use only
    [Classical_Prop.classic]. The demonic ordered-monad instance and reverse
    order comparison are closed. *)
Print Assumptions ASPMonad.dm4all_singleton.
Print Assumptions ASPMonad.dm4all_healthiness.
Print Assumptions ASPMonad.dm4all_to_asp_morphism.
Print Assumptions ASPMonad.asp_to_dm4all_morphism.
Print Assumptions ASPMonad.dm4all_round_trip.
Print Assumptions ASPMonad.asp_dm4all_round_trip.
Print Assumptions ASPMonad.dm4all_to_asp_order.
Print Assumptions ASPMonad.asp_to_dm4all_order.
Print Assumptions ASPMonad.dm4all_ret_true_not_top.
Print Assumptions ASPMonad.dm4all_not_dslp_healthy.
Print Assumptions DSLPMonad.SPostDem.MonadLawsE_SPost.
Print Assumptions DSLPMonad.SPostDem.OrderedMonad_SPost.
Print Assumptions DSLPMonad.dm4all_dem_healthiness.
Print Assumptions DSLPMonad.dm4all_dem_to_dslp_morphism.
Print Assumptions DSLPMonad.dslp_to_dm4all_dem_morphism.
Print Assumptions DSLPMonad.dm4all_dem_round_trip.
Print Assumptions DSLPMonad.dslp_dm4all_dem_round_trip.
Print Assumptions DSLPMonad.dm4all_dem_to_dslp_order.
Print Assumptions DSLPMonad.dslp_to_dm4all_dem_order.


(** Canonical carriers share law dictionaries with their compatibility names.
    ASP/DSLP normal forms and base laws are constructive; DSP/ASLP recovery
    retains excluded middle. Cross-API test clients remain outside this audit. *)
Print Assumptions SPostArr.ASP_normal_form.
Print Assumptions SPostArr.DSLP_normal_form.
Print Assumptions SPostArr.ArrowLaws_ASPArr.
Print Assumptions SPostArr.ArrowChoiceLaws_ASPArr.
Print Assumptions SPostArr.ArrowApplyLaws_ASPArr.
Print Assumptions SPostArr.ArrowLaws_DSLPArr.
Print Assumptions SPostArr.ArrowChoiceLaws_DSLPArr.
Print Assumptions SPostArr.ArrowApplyLaws_DSLPArr.
Print Assumptions DSPASLPArr.ArrowLaws_DSPArr.
Print Assumptions DSPASLPArr.ArrowChoiceLaws_DSPArr.
Print Assumptions DSPASLPArr.ArrowApplyLaws_DSPArr.
Print Assumptions DSPASLPArr.ArrowLaws_ASLPArr.
Print Assumptions DSPASLPArr.ArrowChoiceLaws_ASLPArr.
Print Assumptions DSPASLPArr.ArrowApplyLaws_ASLPArr.

(** Canonical relation readings specialize the generic normalization facts
    through existing RelArrow/RelArrowChoice/RelArrowApply dictionaries.
    These semantic wrappers are constructive. *)
Print Assumptions SPostArr.aspRel_bind.
Print Assumptions SPostArr.aspRelS_bind.
Print Assumptions SPostArr.aspRelO_comp.
Print Assumptions SPostArr.aspRelO_first.
Print Assumptions SPostArr.aspRelE_first.
Print Assumptions SPostArr.aspRelE_app.
Print Assumptions SPostArr.aspRelE_bind.
Print Assumptions SPostArr.dslpRel_bind.
Print Assumptions SPostArr.dslpRelS_bind.
Print Assumptions SPostArr.dslpRelO_comp.
Print Assumptions SPostArr.dslpRelO_first.
Print Assumptions SPostArr.dslpRelE_first.
Print Assumptions SPostArr.dslpRelE_app.
Print Assumptions SPostArr.dslpRelE_bind.

(** Generic base/state bind normalization uses only the semantic dictionaries
    and is closed under the global context. *)
Print Assumptions RelArrowCoherence.rel_bind.
Print Assumptions RelArrowCoherence.relS_bind.

(** * Triples

    Monad morphisms, their lifts through the monad transformers, and the
    monad morphism of an arrow morphism: closed. *)
From Incorrectness.Lib.Monad Require OrderedMonad.
From Incorrectness.Lib.Arrow Require ArrowMorphism.
From Incorrectness.Lib.Monad Require TransformerLaws.
From Incorrectness.Verification.DivNonDet Require
  Morphisms.
From Incorrectness.Verification.DivNonDetSt Require
  Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require
  Morphisms.
From Incorrectness.Verification.Generic Require
  Triple.
From Incorrectness.Verification.DivNonDet Require
  Triples.
From Incorrectness.Verification.DivNonDetSt Require
  Triples.
From Incorrectness.Verification.DivNonDetStExc Require
  Triples.
From Incorrectness.Verification.Generic Require
  TripleTaxonomy.
From Incorrectness.Verification.DivNonDet Require
  TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetSt Require
  TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetStExc Require
  TriplesTaxonomy TriplesExamples.
From Incorrectness.Verification.DivNonDetSt Require
  InCorrectnessPrinciples.
From Incorrectness.Verification.Generic Require DijkstraMonad.
From Incorrectness.Verification.DivNonDet Require DijkstraMonads.
From Incorrectness.Verification.DivNonDetSt Require DijkstraMonads.
From Incorrectness.Verification.DivNonDetStExc Require DijkstraMonads.
From Incorrectness.Verification.Generic Require Typings.
From Incorrectness.Verification.DivNonDet Require Typings.
From Incorrectness.Verification.DivNonDetSt Require Typings.
From Incorrectness.Verification.DivNonDetStExc Require Typings.
From Incorrectness.Verification.DivNonDet Require Typings.
From Incorrectness.Verification.DivNonDetStExc Require DijkstraExamples.
Print Assumptions OrderedMonad.MonadMorphism_comp.
Print Assumptions OrderedMonad.MonadMorphism_ext.
Print Assumptions OrderedMonad.MonadMorphism_of_laws.
Print Assumptions TransformerLaws.MonadMorphism_optionT.
Print Assumptions TransformerLaws.MonadMorphism_stateT.
Print Assumptions ArrowMorphism.arrow_morphism_monad.

(** Base arrow morphisms.  The generic reading is closed; the DSP and ASLP
    instances use excluded middle, as their carriers do. *)
Print Assumptions SPostArrEquiv.rel_reading_morphism.
Print Assumptions SPostArrEquiv.rel_section_morphism.
Print Assumptions SPostArrEquiv.dsp_to_rel_morphism.
Print Assumptions SPostArrEquiv.dsp_from_rel_morphism.
Print Assumptions SPostArrEquiv.aslp_to_rel_morphism.
Print Assumptions SPostArrEquiv.aslp_from_rel_morphism.

(** The WP morphisms out of [divndNE] at the three levels, and the lifting
    of their triples: closed. *)
Print Assumptions Morphisms.dwpPure_morphism.
Print Assumptions Morphisms.dwlpPure_morphism.
Print Assumptions Morphisms.awpPure_morphism.
Print Assumptions Morphisms.awlpPure_morphism.
Print Assumptions Morphisms.dwpSt_morphism.
Print Assumptions Morphisms.dwlpSt_morphism.
Print Assumptions Morphisms.awpSt_morphism.
Print Assumptions Morphisms.awlpSt_morphism.
Print Assumptions Morphisms.dwpStExc_morphism.
Print Assumptions Morphisms.dwlpStExc_morphism.
Print Assumptions Morphisms.awpStExc_morphism.
Print Assumptions Morphisms.awlpStExc_morphism.
Print Assumptions Triples.spec_holds_wpSt.
Print Assumptions Triples.spec_holds_wpStExc.
Print Assumptions Triples.triple_dwpSt.
Print Assumptions Triples.triple_dwpStExc.

(** The SP morphisms.  Obtained by lifting the base arrow morphism through
    the arrow transformers, the morphism theorems above the base inherit
    the functional extensionality of the transformer law packages. *)
Print Assumptions Morphisms.spPure_morphism.
Print Assumptions Morphisms.spSt_morphism.
Print Assumptions Morphisms.spStExc_morphism.
Print Assumptions Morphisms.aspSt_morphism.
Print Assumptions Morphisms.dslpStExc_morphism.
Print Assumptions Morphisms.dspSt_morphism.
Print Assumptions Morphisms.aslpStExc_morphism.

(** The same statements proved through the relations denoted: closed for ASP
    and DSLP, excluded middle for DSP and ASLP.  The [IsMonadMorphism]
    instances are built from these, so a triple carries no more than this. *)
Print Assumptions Morphisms.spPure_morphism_rel.
Print Assumptions Morphisms.spSt_morphism_rel.
Print Assumptions Morphisms.spStExc_morphism_rel.
Print Assumptions Morphisms.aspSt_morphism_rel.
Print Assumptions Morphisms.aspStExc_morphism_rel.
Print Assumptions Morphisms.dslpSt_morphism_rel.
Print Assumptions Morphisms.dslpStExc_morphism_rel.
Print Assumptions Morphisms.dspSt_morphism_rel.
Print Assumptions Morphisms.dspStExc_morphism_rel.
Print Assumptions Morphisms.aslpSt_morphism_rel.
Print Assumptions Morphisms.aslpStExc_morphism_rel.
Print Assumptions Triples.triple_aspSt.
Print Assumptions Triples.triple_aspStExc.
Print Assumptions Triples.triple_dslpSt.
Print Assumptions Triples.triple_dslpStExc.
Print Assumptions Triples.triple_dspSt.
Print Assumptions Triples.triple_dspStExc.
Print Assumptions Triples.triple_aslpSt.
Print Assumptions Triples.triple_aslpStExc.

(** The taxonomy diagram at the state level.

    Implications between WP triples: closed. *)
Print Assumptions TriplesTaxonomy.TotalCorr_impl_PartCorr.
Print Assumptions TriplesTaxonomy.LisbonLogic_impl_AngPartCorr.
Print Assumptions TriplesTaxonomy.TotalCorr_impl_LisbonLogic.
Print Assumptions TriplesTaxonomy.PartCorr_impl_AngPartCorr.
Print Assumptions TriplesTaxonomy.dwlp_over_impl_dwp_over.
Print Assumptions TriplesTaxonomy.awlp_over_impl_awp_over.
Print Assumptions TriplesTaxonomy.awp_over_impl_dwp_over.
Print Assumptions TriplesTaxonomy.awlp_over_impl_dwlp_over.

(** Implications between SP triples: excluded middle, from the DSP and ASLP
    carriers. *)
Print Assumptions TriplesTaxonomy.aslp_over_impl_asp_over.
Print Assumptions TriplesTaxonomy.aslp_over_impl_dslp_over.
Print Assumptions TriplesTaxonomy.asp_over_impl_dsp_over.
Print Assumptions TriplesTaxonomy.dslp_over_impl_dsp_over.
Print Assumptions TriplesTaxonomy.DemIncorr_impl_PartIncorr.
Print Assumptions TriplesTaxonomy.DemIncorr_impl_IncorrLogic.
Print Assumptions TriplesTaxonomy.PartIncorr_impl_AngPartIncorr.
Print Assumptions TriplesTaxonomy.IncorrLogic_impl_AngPartIncorr.

(** Contrapositives: excluded middle. *)
Print Assumptions TriplesTaxonomy.LisbonLogic_contra_dwlp_over.
Print Assumptions TriplesTaxonomy.AngPartCorr_contra_dwp_over.
Print Assumptions TriplesTaxonomy.TotalCorr_contra_awlp_over.
Print Assumptions TriplesTaxonomy.PartCorr_contra_awp_over.
Print Assumptions TriplesTaxonomy.DemIncorr_contra_aslp_over.
Print Assumptions TriplesTaxonomy.PartIncorr_contra_asp_over.
Print Assumptions TriplesTaxonomy.IncorrLogic_contra_dslp_over.
Print Assumptions TriplesTaxonomy.AngPartIncorr_contra_dsp_over.

(** The two Galois edges: closed. *)
Print Assumptions TriplesTaxonomy.PartCorr_galois_asp_over.
Print Assumptions TriplesTaxonomy.awp_over_galois_PartIncorr.

(** One example per triple kind.  The twelve WP, ASP and DSLP examples are
    closed; the four DSP and ASLP examples use excluded middle. *)
Print Assumptions ProgA.progA_dwp_under.
Print Assumptions ProgRet.progRet_dwp_over.
Print Assumptions ProgB.progB_dwlp_under.
Print Assumptions ProgRet.progRet_dwlp_over.
Print Assumptions ProgA.progA_awp_under.
Print Assumptions ProgA.progA_awp_over.
Print Assumptions ProgB.progB_awlp_under.
Print Assumptions ProgRet.progRet_awlp_over.
Print Assumptions ProgA.progA_asp_over.
Print Assumptions ProgA.progA_asp_under.
Print Assumptions ProgEx.progEx_dslp_under.
Print Assumptions ProgA.progA_dslp_over.
Print Assumptions ProgRet.progRet_dsp_under.
Print Assumptions ProgRet.progRet_dsp_over.
Print Assumptions ProgRet.progRet_aslp_under.
Print Assumptions ProgRet.progRet_aslp_over.
Print Assumptions OHearn.example_incorrect.

(** The four healthiness classes are distinct: closed. *)
Print Assumptions DSPASLPArr.no_ASPArr_for_dsp.
Print Assumptions DSPASLPArr.no_DSLPArr_for_dsp.
Print Assumptions DSPASLPArr.no_ASPArr_for_aslp.
Print Assumptions DSPASLPArr.no_DSLPArr_for_aslp.
Print Assumptions DSPASLPArr.no_ASPArr_for_dslp.

(** The diagram with exceptions: the same pattern as at the state level.
    WP implications and Galois edges closed, the rest excluded middle. *)
Print Assumptions TriplesTaxonomy.TotalCorr_impl_PartCorr_exc.
Print Assumptions TriplesTaxonomy.awlp_over_impl_dwlp_over_exc.
Print Assumptions TriplesTaxonomy.PartCorr_galois_asp_over_exc.
Print Assumptions TriplesTaxonomy.awp_over_galois_PartIncorr_exc.
Print Assumptions TriplesTaxonomy.DemIncorr_impl_IncorrLogic_exc.
Print Assumptions TriplesTaxonomy.IncorrLogic_contra_dslp_over_exc.
Print Assumptions TriplesTaxonomy.LisbonLogic_contra_dwlp_over_exc.

(** The rewriting rules, for ASP and for the demonic liberal WP: closed. *)
Print Assumptions InCorrectnessPrinciples.first_symmetry_rule_asp.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_asp.
Print Assumptions InCorrectnessPrinciples.first_imp_symmetry_rule_asp.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule_asp.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement_asp.
Print Assumptions InCorrectnessPrinciples.principle_of_denial_asp.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_dwlp.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule_dwlp.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement_dwlp.
Print Assumptions InCorrectnessPrinciples.principle_of_denial_dwlp.

(** The same rules for any relation, without state, and with state and
    exceptions; the triple-level Galois edge without state. *)
From Incorrectness.Verification.Generic Require InCorrectnessPrinciples.
From Incorrectness.Verification.DivNonDet Require InCorrectnessPrinciples TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetStExc Require InCorrectnessPrinciples.
Print Assumptions InCorrectnessPrinciples.first_symmetry_rule_1.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_1.
Print Assumptions InCorrectnessPrinciples.first_imp_symmetry_rule.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement.
Print Assumptions InCorrectnessPrinciples.principle_of_denial.
Print Assumptions TriplesTaxonomy.PartCorr_galois_asp_over_pure.
Print Assumptions InCorrectnessPrinciples.first_symmetry_rule_aspPure.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_aspPure.
Print Assumptions InCorrectnessPrinciples.first_imp_symmetry_rule_aspPure.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule_aspPure.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement_aspPure.
Print Assumptions InCorrectnessPrinciples.principle_of_denial_aspPure.
Print Assumptions InCorrectnessPrinciples.first_symmetry_rule_aspStExc.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_aspStExc.
Print Assumptions InCorrectnessPrinciples.first_imp_symmetry_rule_aspStExc.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule_aspStExc.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement_aspStExc.
Print Assumptions InCorrectnessPrinciples.principle_of_denial_aspStExc.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_dwlpPure.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule_dwlpPure.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement_dwlpPure.
Print Assumptions InCorrectnessPrinciples.principle_of_denial_dwlpPure.
Print Assumptions InCorrectnessPrinciples.second_symmetry_rule_dwlpStExc.
Print Assumptions InCorrectnessPrinciples.second_imp_symmetry_rule_dwlpStExc.
Print Assumptions InCorrectnessPrinciples.principle_of_agreement_dwlpStExc.
Print Assumptions InCorrectnessPrinciples.principle_of_denial_dwlpStExc.

(** The Dijkstra monad of a monad morphism.  The construction is closed;
    an instance carries the assumptions of its morphism and of the order of
    its target, and the WP, ASP and DSLP ones are closed.  The
    identifications of triples with typings are closed. *)
Print Assumptions DijkstraMonad.DM_bind_typing.
Print Assumptions DijkstraMonad.DMop_bind.

(** The Dijkstra monad laws are the source monad's: closed in general.  At
    the computation monads of this development they inherit functional and
    propositional extensionality from the laws of [SetM]. *)
Print Assumptions DijkstraMonad.DM_laws.
Print Assumptions DijkstraMonad.DMop_laws.
Print Assumptions DijkstraMonads.Ddwp_laws.
Print Assumptions DijkstraMonads.Dasp_op_laws.
Print Assumptions DijkstraMonads.OrderedTarget_dwpStExc.
Print Assumptions DijkstraMonads.OrderedTarget_awlpSt.
Print Assumptions DijkstraMonads.OrderedTarget_aspStExc.
Print Assumptions DijkstraMonads.OrderedTarget_dslpSt.
Print Assumptions Typings.triple_under_wpStExc.
Print Assumptions Typings.triple_over_wpStExc.
Print Assumptions Typings.triple_over_aspStExc.
Print Assumptions Typings.triple_under_dslpStExc.

(** Specification monads: the pulled-back order, submonads, and the four WP
    flavours as submonads of [WPure]: closed. *)
Print Assumptions OrderedMonad.OrderedMonad_flip.
Print Assumptions OrderedMonad.OrderedMonad_pullback.
Print Assumptions OrderedMonad.OrderedMonad_SubMonad.
Print Assumptions WPure.OrderedMonad_WPure.
Print Assumptions WPure.OrderedMonad_WSt.
Print Assumptions WPure.OrderedMonad_WStExc.
Print Assumptions WPVariants.OrderedMonad_WPSub.

(** ASP [Under] and DSLP [Over] are not typings: closed, except that a DSLP
    [Over] typing gives its triple by excluded middle.  Without state the
    ASP [Under] triple is a typing: closed. *)
Print Assumptions Typings.le_aspUnder.
Print Assumptions Typings.dslpOver_le.
Print Assumptions Typings.dslpOver_typing_triple.
Print Assumptions Typings.no_asp_under_index.
Print Assumptions Typings.no_dslp_over_index.
Print Assumptions Typings.triple_under_aspPure.

(** Typed programs.  The WP, ASP and pure ones are closed; the DSLP ones use
    excluded middle. *)
Print Assumptions DijkstraExamples.progA_Ddwp.
Print Assumptions DijkstraExamples.progRet_Ddwp_op.
Print Assumptions DijkstraExamples.progB_Ddwlp.
Print Assumptions DijkstraExamples.progRet_Ddwlp_op.
Print Assumptions DijkstraExamples.progA_Dawp.
Print Assumptions DijkstraExamples.progA_Dawp_op.
Print Assumptions DijkstraExamples.progB_Dawlp.
Print Assumptions DijkstraExamples.progRet_Dawlp_op.
Print Assumptions DijkstraExamples.progA_Dasp.
Print Assumptions DijkstraExamples.progEx_Ddslp_op.
Print Assumptions DijkstraExamples.progA_Dasp_op.
Print Assumptions DijkstraExamples.progloom_harder_not_Dasp_op.
Print Assumptions DijkstraExamples.progA_Ddslp.
Print Assumptions DijkstraExamples.progloom_harder_dslp_over.
Print Assumptions DijkstraExamples.progloom_harder_not_Ddslp.
Print Assumptions Typings.oneOrTwo_Dasp_op.

From Incorrectness.Lib Require ITreeFacts.
From Incorrectness.Verification.DivNonDet Require Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Morphisms.
From Incorrectness.Verification.DivNonDet.TriplesExamples Require ITreePrograms.
From Incorrectness.Verification.DivNonDetSt.TriplesExamples Require ITreePrograms.
From Incorrectness.Verification.DivNonDetStExc.TriplesExamples Require ITreePrograms.

(** ITree programs.  The one-step inversions of [any_infinite] are closed;
    the infinite paths of a [bind] and [leaf_or_infinite] use excluded middle
    or [eq_rect_eq] (through ITree and paco); [denote] at each setting, the
    readings of programs and the examples also use functional and
    propositional extensionality (outcome sets are compared by Leibniz
    equality). *)
Print Assumptions ITreeFacts.any_infiniteF_vis_inv.
Print Assumptions ITreeFacts.any_infinite_ret.
Print Assumptions ITreeFacts.any_infinite_bind_l.
Print Assumptions ITreeFacts.any_infinite_bind_leaf.
Print Assumptions ITreeFacts.any_infinite_bind_inv.
Print Assumptions ITreeFacts.leaf_or_infinite.
Print Assumptions DivNonDet.Computation.denote_morphism.
Print Assumptions DivNonDetSt.Computation.denoteSt_morphism.
Print Assumptions DivNonDetStExc.Computation.denoteStExc_morphism.
Print Assumptions DivNonDet.Morphisms.IsMonadMorphism_dwpPure_denote.
Print Assumptions DivNonDet.Morphisms.IsMonadMorphism_aslpPure_denote.
Print Assumptions DivNonDetSt.Morphisms.IsMonadMorphism_dspSt_denoteSt.
Print Assumptions DivNonDetStExc.Morphisms.IsMonadMorphism_aslpStExc_denoteStExc.
Print Assumptions DivNonDet.TriplesExamples.ITreePrograms.spin_not_dwp.
Print Assumptions DivNonDetSt.TriplesExamples.ITreePrograms.progA_IT_asp_under.
Print Assumptions DivNonDetStExc.TriplesExamples.ITreePrograms.progA_IT_dwp_under.

(** Further results, expected to use at most excluded middle, functional
    and propositional extensionality. *)
From Incorrectness.SP Require
  LawCounterexamples StatefulSPostCounterexample.
From Incorrectness.PTMonadTaxonomy Require MonadTaxonomy.
From Incorrectness.Verification.DivNonDet Require HealthyReadings.
From Incorrectness.Verification.DivNonDetSt Require
  HealthyReadings TripleRules.
From Incorrectness.Verification.DivNonDetSt.TriplesExamples Require
  ResetEven DSPSequencing.
Print Assumptions StatefulSPostCounterexample.Dem.FailingBind.SPostDem_bind_bind_fails.
Print Assumptions LawCounterexamples.AngArr.not_ArrowLaws.
Print Assumptions ASPMonad.toArrowASPState_morphism.
Print Assumptions ASPMonad.fromArrowASPState_morphism.
Print Assumptions MonadTaxonomy.MonadRelation_asp_implies_aslp_pure.
Print Assumptions DivNonDetSt.TripleRules.wpSt_bind_under.
Print Assumptions DivNonDet.HealthyReadings.dwpPure_DWP_morphism.
Print Assumptions DivNonDet.HealthyReadings.dwpPure_DWP_complete.
Print Assumptions DivNonDetSt.HealthyReadings.dwpSt_DWPSt_morphism.
Print Assumptions DivNonDetSt.TripleRules.aspSt_bind_under.
Print Assumptions DivNonDetSt.TripleRules.dspSt_bind_under.
Print Assumptions ResetEven.incorr_p_q.
Print Assumptions ResetEven.m_DM.
Print Assumptions DSPSequencing.dspSt_over_seq_counterexample.
