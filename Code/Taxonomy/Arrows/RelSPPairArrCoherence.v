(** * Standard application coherence for coupled SP arrows.

    The coupled relation projections give faithful presentations for
    [RelArrowCoherence].  Its generic proofs establish the three standard
    application equations for the pure, option, state, and state-over-option
    carriers below, using Leibniz equality.

    The concrete equalities inherit functional extensionality,
    propositional extensionality, and proof irrelevance from the bundled
    equality lemmas. *)

From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import RelSPPairArr.
From Incorrectness.Classes Require Export RelArrowCoherence.

(** Compatibility aliases retain the module-qualified API after moving
    faithfulness and presentation witnesses into the core law module. *)
Definition ASP_rel_ext := @RelSPPairArr.ASP_rel_ext.
Arguments ASP_rel_ext {A B} f g _.
Definition DSLP_rel_ext := @RelSPPairArr.DSLP_rel_ext.
Arguments DSLP_rel_ext {A B} f g _.
Definition ASP_rel_presentation := RelSPPairArr.ASP_rel_presentation.
Definition DSLP_rel_presentation := RelSPPairArr.DSLP_rel_presentation.

(** ** Concrete API

    Each carrier exposes [_app_unit], [_app_precompose], and
    [_app_postcompose].  Local operation notations fix the intended
    transformer instances, even though all carriers unfold to sigma types. *)

Section ASPCoherence.
  Local Notation pure := (@arr_pure PureASPostArr Arrow_PureASPostArr).
  Local Notation comp := (@arr_comp PureASPostArr Arrow_PureASPostArr).
  Local Notation first := (@arr_first PureASPostArr Arrow_PureASPostArr).
  Local Notation second := (@arr_second PureASPostArr Arrow_PureASPostArr).
  Local Notation app :=
    (@arr_app PureASPostArr Arrow_PureASPostArr ArrowApply_PureASPostArr).

  Lemma ASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id PureASPostArr Arrow_PureASPostArr (A * B).
  Proof. exact (rel_app_unit ASP_rel_presentation A B). Qed.

  Lemma ASP_app_precompose {A B C} (g : PureASPostArr A B) :
    comp (first (pure (fun f : PureASPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_app_precompose ASP_rel_presentation g). Qed.

  Lemma ASP_app_postcompose {A B C} (h : PureASPostArr B C) :
    comp (first (pure (fun f : PureASPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_app_postcompose ASP_rel_presentation h). Qed.
End ASPCoherence.

Section DSLPCoherence.
  Local Notation pure := (@arr_pure PureDSLPostArr Arrow_PureDSLPostArr).
  Local Notation comp := (@arr_comp PureDSLPostArr Arrow_PureDSLPostArr).
  Local Notation first := (@arr_first PureDSLPostArr Arrow_PureDSLPostArr).
  Local Notation second := (@arr_second PureDSLPostArr Arrow_PureDSLPostArr).
  Local Notation app :=
    (@arr_app PureDSLPostArr Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr).

  Lemma DSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id PureDSLPostArr Arrow_PureDSLPostArr (A * B).
  Proof. exact (rel_app_unit DSLP_rel_presentation A B). Qed.

  Lemma DSLP_app_precompose {A B C} (g : PureDSLPostArr A B) :
    comp (first (pure (fun f : PureDSLPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_app_precompose DSLP_rel_presentation g). Qed.

  Lemma DSLP_app_postcompose {A B C} (h : PureDSLPostArr B C) :
    comp (first (pure (fun f : PureDSLPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_app_postcompose DSLP_rel_presentation h). Qed.
End DSLPCoherence.

Section OptionASPCoherence.
  Local Notation HA :=
    (@Arrow_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr).
  Local Notation pure := (@arr_pure optionASPArr HA).
  Local Notation comp := (@arr_comp optionASPArr HA).
  Local Notation first := (@arr_first optionASPArr HA).
  Local Notation second := (@arr_second optionASPArr HA).
  Local Notation app := (@arr_app optionASPArr HA
    (@ArrowApply_optionArrT PureASPostArr Arrow_PureASPostArr
      ArrowChoice_PureASPostArr ArrowApply_PureASPostArr)).

  Lemma optionASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id optionASPArr HA (A * B).
  Proof. exact (rel_option_app_unit ASP_rel_presentation A B). Qed.

  Lemma optionASP_app_precompose {A B C} (g : optionASPArr A B) :
    comp (first (pure (fun f : optionASPArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_option_app_precompose ASP_rel_presentation g). Qed.

  Lemma optionASP_app_postcompose {A B C} (h : optionASPArr B C) :
    comp (first (pure (fun f : optionASPArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_option_app_postcompose ASP_rel_presentation h). Qed.
End OptionASPCoherence.

Section OptionDSLPCoherence.
  Local Notation HA :=
    (@Arrow_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr).
  Local Notation pure := (@arr_pure optionDSLPArr HA).
  Local Notation comp := (@arr_comp optionDSLPArr HA).
  Local Notation first := (@arr_first optionDSLPArr HA).
  Local Notation second := (@arr_second optionDSLPArr HA).
  Local Notation app := (@arr_app optionDSLPArr HA
    (@ArrowApply_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
      ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr)).

  Lemma optionDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id optionDSLPArr HA (A * B).
  Proof. exact (rel_option_app_unit DSLP_rel_presentation A B). Qed.

  Lemma optionDSLP_app_precompose {A B C} (g : optionDSLPArr A B) :
    comp (first (pure (fun f : optionDSLPArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_option_app_precompose DSLP_rel_presentation g). Qed.

  Lemma optionDSLP_app_postcompose {A B C} (h : optionDSLPArr B C) :
    comp (first (pure (fun f : optionDSLPArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_option_app_postcompose DSLP_rel_presentation h). Qed.
End OptionDSLPCoherence.

Section StateASPCoherence.
  Variable S : Type.
  Local Notation HA := (@Arrow_stateArrT S PureASPostArr Arrow_PureASPostArr).
  Local Notation pure := (@arr_pure (stateArrT S PureASPostArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S PureASPostArr) HA).
  Local Notation first := (@arr_first (stateArrT S PureASPostArr) HA).
  Local Notation second := (@arr_second (stateArrT S PureASPostArr) HA).
  Local Notation app := (@arr_app (stateArrT S PureASPostArr) HA
    (@ArrowApply_stateArrT S PureASPostArr Arrow_PureASPostArr ArrowApply_PureASPostArr)).

  Lemma stateASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S PureASPostArr) HA (A * B).
  Proof. exact (rel_state_app_unit ASP_rel_presentation S A B). Qed.

  Lemma stateASP_app_precompose {A B C} (g : stateArrT S PureASPostArr A B) :
    comp (first (pure (fun f : stateArrT S PureASPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_state_app_precompose ASP_rel_presentation S g). Qed.

  Lemma stateASP_app_postcompose {A B C} (h : stateArrT S PureASPostArr B C) :
    comp (first (pure (fun f : stateArrT S PureASPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_state_app_postcompose ASP_rel_presentation S h). Qed.
End StateASPCoherence.

Section StateDSLPCoherence.
  Variable S : Type.
  Local Notation HA := (@Arrow_stateArrT S PureDSLPostArr Arrow_PureDSLPostArr).
  Local Notation pure := (@arr_pure (stateArrT S PureDSLPostArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S PureDSLPostArr) HA).
  Local Notation first := (@arr_first (stateArrT S PureDSLPostArr) HA).
  Local Notation second := (@arr_second (stateArrT S PureDSLPostArr) HA).
  Local Notation app := (@arr_app (stateArrT S PureDSLPostArr) HA
    (@ArrowApply_stateArrT S PureDSLPostArr Arrow_PureDSLPostArr
      ArrowApply_PureDSLPostArr)).

  Lemma stateDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S PureDSLPostArr) HA (A * B).
  Proof. exact (rel_state_app_unit DSLP_rel_presentation S A B). Qed.

  Lemma stateDSLP_app_precompose {A B C} (g : stateArrT S PureDSLPostArr A B) :
    comp (first (pure (fun f : stateArrT S PureDSLPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_state_app_precompose DSLP_rel_presentation S g). Qed.

  Lemma stateDSLP_app_postcompose {A B C} (h : stateArrT S PureDSLPostArr B C) :
    comp (first (pure (fun f : stateArrT S PureDSLPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_state_app_postcompose DSLP_rel_presentation S h). Qed.
End StateDSLPCoherence.

Section StateOptionASPCoherence.
  Variable S : Type.
  Local Notation OA :=
    (@Arrow_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr).
  Local Notation HA := (@Arrow_stateArrT S optionASPArr OA).
  Local Notation pure := (@arr_pure (stateArrT S optionASPArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S optionASPArr) HA).
  Local Notation first := (@arr_first (stateArrT S optionASPArr) HA).
  Local Notation second := (@arr_second (stateArrT S optionASPArr) HA).
  Local Notation app := (@arr_app (stateArrT S optionASPArr) HA
    (@ArrowApply_stateArrT S optionASPArr OA
      (@ArrowApply_optionArrT PureASPostArr Arrow_PureASPostArr
        ArrowChoice_PureASPostArr ArrowApply_PureASPostArr))).

  Lemma stateOptASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S optionASPArr) HA (A * B).
  Proof. exact (rel_state_option_app_unit ASP_rel_presentation S A B). Qed.

  Lemma stateOptASP_app_precompose {A B C} (g : stateArrT S optionASPArr A B) :
    comp (first (pure (fun f : stateArrT S optionASPArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_state_option_app_precompose ASP_rel_presentation S g). Qed.

  Lemma stateOptASP_app_postcompose {A B C} (h : stateArrT S optionASPArr B C) :
    comp (first (pure (fun f : stateArrT S optionASPArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_state_option_app_postcompose ASP_rel_presentation S h). Qed.
End StateOptionASPCoherence.

Section StateOptionDSLPCoherence.
  Variable S : Type.
  Local Notation OA :=
    (@Arrow_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr).
  Local Notation HA := (@Arrow_stateArrT S optionDSLPArr OA).
  Local Notation pure := (@arr_pure (stateArrT S optionDSLPArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S optionDSLPArr) HA).
  Local Notation first := (@arr_first (stateArrT S optionDSLPArr) HA).
  Local Notation second := (@arr_second (stateArrT S optionDSLPArr) HA).
  Local Notation app := (@arr_app (stateArrT S optionDSLPArr) HA
    (@ArrowApply_stateArrT S optionDSLPArr OA
      (@ArrowApply_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
        ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr))).

  Lemma stateOptDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S optionDSLPArr) HA (A * B).
  Proof. exact (rel_state_option_app_unit DSLP_rel_presentation S A B). Qed.

  Lemma stateOptDSLP_app_precompose {A B C} (g : stateArrT S optionDSLPArr A B) :
    comp (first (pure (fun f : stateArrT S optionDSLPArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_state_option_app_precompose DSLP_rel_presentation S g). Qed.

  Lemma stateOptDSLP_app_postcompose {A B C} (h : stateArrT S optionDSLPArr B C) :
    comp (first (pure (fun f : stateArrT S optionDSLPArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_state_option_app_postcompose DSLP_rel_presentation S h). Qed.
End StateOptionDSLPCoherence.
