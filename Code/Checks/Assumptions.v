(** Console assumption reports, compiled explicitly by [make check]. *)
From Incorrectness.Classes Require Import
  Arrow ArrowApplyFacts ArrowMonad OptionArrowT StateArrowT RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import
  SPostArr RelSPostArr SPostArrEquiv GaloisArr Rel PrePostArr RelPrePostArr WPArr.
From Incorrectness.Classes.Tests Require Import ArrowMonadRegression.
From Incorrectness.Taxonomy.BaseSpecMonads Require ASPMonad DSLPMonad DSPMonad
  ASLPMonad BaseGaloisConnections.
From Incorrectness.Taxonomy.ComputationMonads Require Import DivNonDetNE.

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
Print Assumptions WrongIndex.arrow_laws.

(** Computation-owned outcome laws use pointwise equivalence and are
    closed under the global context. *)
Print Assumptions DivNonDetNE.outcomes_bind.
Print Assumptions DivNonDetNE.diverge_absorbing.
Print Assumptions DivNonDetNE.empty_prefix_blocks.
Print Assumptions DivNonDetNE.outSt_bind.
Print Assumptions DivNonDetNE.outStExc_bind.

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

(** * Triples

    Monad morphisms, their lifts through the monad transformers, and the
    monad morphism of an arrow morphism: closed. *)
From Incorrectness.Classes Require OrderedMonad ArrowMorphism.
From Incorrectness.Taxonomy.ComputationMonads Require TransformerLaws.
From Incorrectness.Taxonomy.Triples Require MonadMorphisms Diagram Examples
  InCorrectnessPrinciples.
From Incorrectness.Taxonomy.DijkstraMonads Require DijkstraMonad DijkstraExamples.
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
Print Assumptions MonadMorphisms.dwpPure_morphism.
Print Assumptions MonadMorphisms.dwlpPure_morphism.
Print Assumptions MonadMorphisms.awpPure_morphism.
Print Assumptions MonadMorphisms.awlpPure_morphism.
Print Assumptions MonadMorphisms.dwpSt_morphism.
Print Assumptions MonadMorphisms.dwlpSt_morphism.
Print Assumptions MonadMorphisms.awpSt_morphism.
Print Assumptions MonadMorphisms.awlpSt_morphism.
Print Assumptions MonadMorphisms.dwpStExc_morphism.
Print Assumptions MonadMorphisms.dwlpStExc_morphism.
Print Assumptions MonadMorphisms.awpStExc_morphism.
Print Assumptions MonadMorphisms.awlpStExc_morphism.
Print Assumptions MonadMorphisms.spec_holds_wpSt.
Print Assumptions MonadMorphisms.spec_holds_wpStExc.
Print Assumptions MonadMorphisms.triple_dwpSt.
Print Assumptions MonadMorphisms.triple_dwpStExc.

(** The SP morphisms.  Obtained by lifting the base arrow morphism through
    the arrow transformers, the morphism theorems above the base inherit
    the functional extensionality of the transformer law packages. *)
Print Assumptions MonadMorphisms.spPure_morphism.
Print Assumptions MonadMorphisms.spSt_morphism.
Print Assumptions MonadMorphisms.spStExc_morphism.
Print Assumptions MonadMorphisms.aspSt_morphism.
Print Assumptions MonadMorphisms.dslpStExc_morphism.
Print Assumptions MonadMorphisms.dspSt_morphism.
Print Assumptions MonadMorphisms.aslpStExc_morphism.

(** The same statements proved through the relations denoted: closed for ASP
    and DSLP, excluded middle for DSP and ASLP.  The [IsMonadMorphism]
    instances are built from these, so a triple carries no more than this. *)
Print Assumptions MonadMorphisms.spPure_morphism_rel.
Print Assumptions MonadMorphisms.spSt_morphism_rel.
Print Assumptions MonadMorphisms.spStExc_morphism_rel.
Print Assumptions MonadMorphisms.aspSt_morphism_rel.
Print Assumptions MonadMorphisms.aspStExc_morphism_rel.
Print Assumptions MonadMorphisms.dslpSt_morphism_rel.
Print Assumptions MonadMorphisms.dslpStExc_morphism_rel.
Print Assumptions MonadMorphisms.dspSt_morphism_rel.
Print Assumptions MonadMorphisms.dspStExc_morphism_rel.
Print Assumptions MonadMorphisms.aslpSt_morphism_rel.
Print Assumptions MonadMorphisms.aslpStExc_morphism_rel.
Print Assumptions MonadMorphisms.triple_aspSt.
Print Assumptions MonadMorphisms.triple_aspStExc.
Print Assumptions MonadMorphisms.triple_dslpSt.
Print Assumptions MonadMorphisms.triple_dslpStExc.
Print Assumptions MonadMorphisms.triple_dspSt.
Print Assumptions MonadMorphisms.triple_dspStExc.
Print Assumptions MonadMorphisms.triple_aslpSt.
Print Assumptions MonadMorphisms.triple_aslpStExc.

(** The taxonomy diagram at the state level.

    Implications between WP triples: closed. *)
Print Assumptions Diagram.dwp_under_dwlp_under.
Print Assumptions Diagram.awp_under_awlp_under.
Print Assumptions Diagram.dwp_under_awp_under.
Print Assumptions Diagram.dwlp_under_awlp_under.
Print Assumptions Diagram.dwlp_over_dwp_over.
Print Assumptions Diagram.awlp_over_awp_over.
Print Assumptions Diagram.awp_over_dwp_over.
Print Assumptions Diagram.awlp_over_dwlp_over.

(** Implications between SP triples: excluded middle, from the DSP and ASLP
    carriers. *)
Print Assumptions Diagram.aslp_over_asp_over.
Print Assumptions Diagram.aslp_over_dslp_over.
Print Assumptions Diagram.asp_over_dsp_over.
Print Assumptions Diagram.dslp_over_dsp_over.
Print Assumptions Diagram.dsp_under_dslp_under.
Print Assumptions Diagram.dsp_under_asp_under.
Print Assumptions Diagram.dslp_under_aslp_under.
Print Assumptions Diagram.asp_under_aslp_under.

(** Contrapositives: excluded middle. *)
Print Assumptions Diagram.awp_under_contra_dwlp_over.
Print Assumptions Diagram.awlp_under_contra_dwp_over.
Print Assumptions Diagram.dwp_under_contra_awlp_over.
Print Assumptions Diagram.dwlp_under_contra_awp_over.
Print Assumptions Diagram.dsp_under_contra_aslp_over.
Print Assumptions Diagram.dslp_under_contra_asp_over.
Print Assumptions Diagram.asp_under_contra_dslp_over.
Print Assumptions Diagram.aslp_under_contra_dsp_over.

(** The two Galois edges: closed. *)
Print Assumptions Diagram.dwlp_under_galois_asp_over.
Print Assumptions Diagram.awp_over_galois_dslp_under.

(** One example per triple kind.  The twelve WP, ASP and DSLP examples are
    closed; the four DSP and ASLP examples use excluded middle. *)
Print Assumptions Examples.progA_dwp_under.
Print Assumptions Examples.progRet_dwp_over.
Print Assumptions Examples.progB_dwlp_under.
Print Assumptions Examples.progRet_dwlp_over.
Print Assumptions Examples.progA_awp_under.
Print Assumptions Examples.progA_awp_over.
Print Assumptions Examples.progB_awlp_under.
Print Assumptions Examples.progRet_awlp_over.
Print Assumptions Examples.progA_asp_over.
Print Assumptions Examples.progA_asp_under.
Print Assumptions Examples.progEx_dslp_under.
Print Assumptions Examples.progA_dslp_over.
Print Assumptions Examples.progRet_dsp_under.
Print Assumptions Examples.progRet_dsp_over.
Print Assumptions Examples.progRet_aslp_under.
Print Assumptions Examples.progRet_aslp_over.
Print Assumptions Examples.example_incorrect.

(** The four healthiness classes are distinct: closed. *)
Print Assumptions SPostArr.no_ASPArr_for_dsp.
Print Assumptions SPostArr.no_DSLPArr_for_dsp.
Print Assumptions SPostArr.no_ASPArr_for_aslp.
Print Assumptions SPostArr.no_DSLPArr_for_aslp.
Print Assumptions SPostArr.no_ASPArr_for_dslp.

(** The diagram with exceptions: the same pattern as at the state level.
    WP implications and Galois edges closed, the rest excluded middle. *)
Print Assumptions Diagram.dwp_under_dwlp_under_exc.
Print Assumptions Diagram.awlp_over_dwlp_over_exc.
Print Assumptions Diagram.dwlp_under_galois_asp_over_exc.
Print Assumptions Diagram.awp_over_galois_dslp_under_exc.
Print Assumptions Diagram.dsp_under_asp_under_exc.
Print Assumptions Diagram.asp_under_contra_dslp_over_exc.
Print Assumptions Diagram.awp_under_contra_dwlp_over_exc.

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
Print Assumptions DijkstraMonad.Ddwp_laws.
Print Assumptions DijkstraMonad.Dasp_op_laws.
Print Assumptions DijkstraMonad.OrderedTarget_dwpStExc.
Print Assumptions DijkstraMonad.OrderedTarget_awlpSt.
Print Assumptions DijkstraMonad.OrderedTarget_aspStExc.
Print Assumptions DijkstraMonad.OrderedTarget_dslpSt.
Print Assumptions DijkstraMonad.triple_under_wpStExc.
Print Assumptions DijkstraMonad.triple_over_wpStExc.
Print Assumptions DijkstraMonad.triple_over_aspStExc.
Print Assumptions DijkstraMonad.triple_under_dslpStExc.

(** Specification monads: the pulled-back order, submonads, and the four WP
    flavours as submonads of [WPure]: closed. *)
Print Assumptions OrderedMonad.OrderedMonad_flip.
Print Assumptions OrderedMonad.OrderedMonad_pullback.
Print Assumptions OrderedMonad.OrderedMonad_SubMonad.
Print Assumptions WPureMonad.OrderedMonad_WPure.
Print Assumptions WPureMonad.OrderedMonad_WSt.
Print Assumptions WPureMonad.OrderedMonad_WStExc.
Print Assumptions WPureMonad.OrderedMonad_WPSub.

(** ASP [Under] and DSLP [Over] are not typings: closed, except that a DSLP
    [Over] typing gives its triple by excluded middle.  Without state the
    ASP [Under] triple is a typing: closed. *)
Print Assumptions DijkstraMonad.le_aspUnder.
Print Assumptions DijkstraMonad.dslpOver_le.
Print Assumptions DijkstraMonad.dslpOver_typing_triple.
Print Assumptions DijkstraMonad.no_asp_under_index.
Print Assumptions DijkstraMonad.no_dslp_over_index.
Print Assumptions DijkstraMonad.triple_under_aspPure.

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
Print Assumptions DijkstraExamples.oneOrTwo_Dasp_op.
