(** Console assumption reports, compiled explicitly by [make check]. *)
From Incorrectness.Classes Require Import RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StExcNonDet_SPostArr StDivNonDet_SPostArr
  StDivITree_SPostArr StDivExcNonDet_SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPBindOrderCounterexample.

(** Generic coherence and the core ASP-to-DSLP bind law. *)
Print Assumptions RelArrowCoherence.rel_state_option_bind.
Print Assumptions SPostArrMonad.asp_to_dslp_bind.

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
