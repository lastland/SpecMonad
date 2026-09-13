(** Console assumption reports, compiled explicitly by [make check]. *)
From Incorrectness.Classes Require Import RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad GaloisArr.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StExcNonDet_SPostArr StDivNonDet_SPostArr
  StDivITree_SPostArr StDivExcNonDet_SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPBindOrderCounterexample.

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
Check Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.dsp_counterexample.
Check Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.aslp_counterexample.
Check Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.dsp_bind_not_monotone.
Check Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.aslp_bind_not_monotone.

Print Assumptions Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.dsp_bind_not_monotone.
Print Assumptions Incorrectness.Taxonomy.BaseSpecMonads.SPBindOrderCounterexample.SPBindOrderCounterexample.aslp_bind_not_monotone.
