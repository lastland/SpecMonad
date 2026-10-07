(** Console assumption reports, compiled explicitly by [make check]. *)
From Incorrectness.Classes Require Import
  Arrow ArrowApplyFacts ArrowMonad OptionArrowT StateArrowT RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import
  SPostArr RelSPostArr SPostArrEquiv GaloisArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StExcNonDet_SPostArr StDivNonDet_SPostArr
  StDivITree_SPostArr StDivExcNonDet_SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPBindOrderCounterexample.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  StExcNonDet StDivNonDet StDivExcNonDet.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import DivExcNonDet_SPDivExc.

(** Shared algebraic helpers take their congruence/application premises
    explicitly. Generic monad laws derive pure congruence constructively;
    transformer law packages retain their existing extensionality dependency. *)
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

(** Computation-owned raw outcome laws use pointwise equivalence and are
    closed under the global context. *)
Print Assumptions StExcNonDet.outcomes_ret.
Print Assumptions StExcNonDet.outcomes_bind.
Print Assumptions StExcNonDet.outcomes_get.
Print Assumptions StExcNonDet.outcomes_put.
Print Assumptions StExcNonDet.outcomes_raise.
Print Assumptions StDivNonDet.outcomes_diverge.
Print Assumptions StDivExcNonDet.outcomes_ret.
Print Assumptions StDivExcNonDet.outcomes_bind.
Print Assumptions StDivExcNonDet.outcomes_get.
Print Assumptions StDivExcNonDet.outcomes_put.
Print Assumptions StDivExcNonDet.outcomes_raise.
Print Assumptions StDivExcNonDet.outcomes_pickP.
Print Assumptions StDivExcNonDet.outcomes_spin.

(** WP return laws support independent state and result types. *)
Print Assumptions StDivExcNonDet_WStExc.obsDWP_ret.
Print Assumptions StDivExcNonDet_WStExc.obsDWLP_ret.
Print Assumptions StDivExcNonDet_WStExc.obsAWP_ret.
Print Assumptions StDivExcNonDet_WStExc.obsAWLP_ret.

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

(** Generic coherence and concrete return readings: axiom-free. *)
Print Assumptions RelArrowCoherence.rel_state_option_bind_fields.
Print Assumptions RelArrowCoherence.rel_state_option_bind.
Print Assumptions SPostArrMonad.ASP_rel_ret.
Print Assumptions SPostArrMonad.DSLP_rel_ret.

(** Concrete bind readings still depend on the SP normal forms; the
    conversion laws additionally conclude equality of packaged arrows. *)
Print Assumptions SPostArrMonad.ASP_rel_bind.
Print Assumptions SPostArrMonad.DSLP_rel_bind.
Print Assumptions SPostArrMonad.asp_to_dslp_ret.
Print Assumptions SPostArrMonad.asp_to_dslp_bind.

(** The adjunction is axiom-free.  DSP shape well-formedness is also
    axiom-free; ASLP shape well-formedness uses excluded middle only. *)
Print Assumptions GaloisArr.adjunction_RPP_WP.
Print Assumptions GaloisArr.Galois_RPP_WP.
Print Assumptions DSPMonad.dsp_shape_wf.
Print Assumptions DSPMonad.StDSP.dsp_shape_wf.
Print Assumptions ASLPMonad.aslp_shape_wf.
Print Assumptions ASLPMonad.StASLP.aslp_shape_wf.

(** Single-option observations and their examples. *)
Print Assumptions StExcNonDet_SPostArr.obsASP_bind.
Print Assumptions StExcNonDet_SPostArr.obsDSLP_bind.
Print Assumptions StExcNonDet_SPostArr.raiser_may_raise.
Print Assumptions StExcNonDet_SPostArr.raiser_dslp.
Print Assumptions StExcNonDet_SPostArr.progA_under.
Print Assumptions StExcNonDet_SPostArr.progA_asp_over.
Print Assumptions StExcNonDet_SPostArr.progA_dslp_under.
Print Assumptions StExcNonDet_SPostArr.progA_dslp_over.
Print Assumptions StExcNonDet_SPostArr.obs_bind_compute.
Print Assumptions StExcNonDet_SPostArr.getEven_under.

Print Assumptions StDivNonDet_SPostArr.obsASP_bind.
Print Assumptions StDivNonDet_SPostArr.obsDSLP_bind.
Print Assumptions StDivNonDet_SPostArr.diverge_asp.
Print Assumptions StDivNonDet_SPostArr.diverge_dslp.
Print Assumptions StDivNonDet_SPostArr.progA_nd_under.
Print Assumptions StDivNonDet_SPostArr.progA_nd_asp_over.
Print Assumptions StDivNonDet_SPostArr.progA_nd_dslp_under.
Print Assumptions StDivNonDet_SPostArr.progA_nd_dslp_over.
Print Assumptions StDivNonDet_SPostArr.obs_bind_compute.

(** Representative ITree and double-option observation laws. *)
Print Assumptions StDivITree_SPostArr.obsASP_bind.
Print Assumptions StDivITree_SPostArr.obsDSLP_bind.
Print Assumptions StDivExcNonDet_SPostArr.obsASP_bind.
Print Assumptions StDivExcNonDet_SPostArr.obsDSLP_bind.

(** Ordered-bind counterexamples. *)
Print Assumptions Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.dsp_bind_not_monotone.
Print Assumptions Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.aslp_bind_not_monotone.

Print Assumptions Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.dsp_arbitrary_bind_impossible.
Print Assumptions Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.aslp_arbitrary_bind_impossible.

(** Stateless ordered binds, with both exceptions and divergence retained. *)
Print Assumptions DSPMonad.bindDSP_mono.
Print Assumptions ASLPMonad.bindASLP_mono.
Print Assumptions TransformerLaws.bind_optionT_mono.
Print Assumptions DivExcSP.bindDSPDivExc_mono.
Print Assumptions DivExcSP.bindASLPDivExc_mono.
Print Assumptions DivExcSP.MonadLawsE__DSPDivExc.
Print Assumptions DivExcSP.MonadLawsE__ASLPDivExc.

Print Assumptions DivExcNonDet.outcomes_ret.
Print Assumptions DivExcNonDet.outcomes_bind.
Print Assumptions DivExcNonDet.outcomes_raise.
Print Assumptions DivExcNonDet.outcomes_spin.
Print Assumptions DivExcNonDet.outcomes_orP.
Print Assumptions DivExcNonDet.MonadLawsE__divexcnd.
Print Assumptions DivExcNonDet_SPDivExc.obsDSP_ret.
Print Assumptions DivExcNonDet_SPDivExc.obsASLP_ret.
Print Assumptions DivExcNonDet_SPDivExc.obsDSP_bind.
Print Assumptions DivExcNonDet_SPDivExc.obsASLP_bind.
Print Assumptions DivExcNonDet_SPDivExc.mixed_DSP_outcomes.
Print Assumptions DivExcNonDet_SPDivExc.mixed_ASLP_outcomes.

(** Canonical carriers share law dictionaries with their compatibility names.
    ASP/DSLP normal forms and base laws are constructive; DSP/ASLP recovery
    retains excluded middle. Cross-API clients check the selected dictionaries
    without reflecting pointwise equivalence into bundled equality. *)
From Incorrectness.Taxonomy.Arrows.Tests Require Import ArrowMonadInstances.
Print Assumptions SPostArr.ASP_normal_form.
Print Assumptions SPostArr.DSLP_normal_form.
Print Assumptions SPostArr.ArrowLaws_ASPArr.
Print Assumptions SPostArr.ArrowChoiceLaws_ASPArr.
Print Assumptions SPostArr.ArrowApplyLaws_ASPArr.
Print Assumptions SPostArr.ArrowLaws_DSLPArr.
Print Assumptions SPostArr.ArrowChoiceLaws_DSLPArr.
Print Assumptions SPostArr.ArrowApplyLaws_DSLPArr.
Print Assumptions SPostArr.ArrowLaws_DSPArr.
Print Assumptions SPostArr.ArrowChoiceLaws_DSPArr.
Print Assumptions SPostArr.ArrowApplyLaws_DSPArr.
Print Assumptions SPostArr.ArrowLaws_ASLPArr.
Print Assumptions SPostArr.ArrowChoiceLaws_ASLPArr.
Print Assumptions SPostArr.ArrowApplyLaws_ASLPArr.

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

Print Assumptions CanonicalSP.asp_mixed_application.
Print Assumptions CanonicalSP.dslp_mixed_application.
Print Assumptions CanonicalSP.asp_mixed_bind_identity.
Print Assumptions CanonicalSP.dslp_mixed_bind_identity.
Print Assumptions CanonicalSP.mixed_update_failure.

(** Generic base/state bind normalization uses only the semantic dictionaries
    and is closed under the global context. *)
Print Assumptions RelArrowCoherence.rel_bind.
Print Assumptions RelArrowCoherence.relS_bind.
