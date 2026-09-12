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
  Local Notation pure := (@arr_pure PureRelASPPairArr Arrow_PureRelASPPairArr).
  Local Notation comp := (@arr_comp PureRelASPPairArr Arrow_PureRelASPPairArr).
  Local Notation first := (@arr_first PureRelASPPairArr Arrow_PureRelASPPairArr).
  Local Notation second := (@arr_second PureRelASPPairArr Arrow_PureRelASPPairArr).
  Local Notation app :=
    (@arr_app PureRelASPPairArr Arrow_PureRelASPPairArr ArrowApply_PureRelASPPairArr).

  Lemma ASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id PureRelASPPairArr Arrow_PureRelASPPairArr (A * B).
  Proof. exact (rel_app_unit ASP_rel_presentation A B). Qed.

  Lemma ASP_app_precompose {A B C} (g : PureRelASPPairArr A B) :
    comp (first (pure (fun f : PureRelASPPairArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_app_precompose ASP_rel_presentation g). Qed.

  Lemma ASP_app_postcompose {A B C} (h : PureRelASPPairArr B C) :
    comp (first (pure (fun f : PureRelASPPairArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_app_postcompose ASP_rel_presentation h). Qed.
End ASPCoherence.

Section DSLPCoherence.
  Local Notation pure := (@arr_pure PureRelDSLPPairArr Arrow_PureRelDSLPPairArr).
  Local Notation comp := (@arr_comp PureRelDSLPPairArr Arrow_PureRelDSLPPairArr).
  Local Notation first := (@arr_first PureRelDSLPPairArr Arrow_PureRelDSLPPairArr).
  Local Notation second := (@arr_second PureRelDSLPPairArr Arrow_PureRelDSLPPairArr).
  Local Notation app :=
    (@arr_app PureRelDSLPPairArr Arrow_PureRelDSLPPairArr ArrowApply_PureRelDSLPPairArr).

  Lemma DSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id PureRelDSLPPairArr Arrow_PureRelDSLPPairArr (A * B).
  Proof. exact (rel_app_unit DSLP_rel_presentation A B). Qed.

  Lemma DSLP_app_precompose {A B C} (g : PureRelDSLPPairArr A B) :
    comp (first (pure (fun f : PureRelDSLPPairArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_app_precompose DSLP_rel_presentation g). Qed.

  Lemma DSLP_app_postcompose {A B C} (h : PureRelDSLPPairArr B C) :
    comp (first (pure (fun f : PureRelDSLPPairArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_app_postcompose DSLP_rel_presentation h). Qed.
End DSLPCoherence.

Section OptionASPCoherence.
  Local Notation HA :=
    (@Arrow_optionArrT PureRelASPPairArr Arrow_PureRelASPPairArr ArrowChoice_PureRelASPPairArr).
  Local Notation pure := (@arr_pure optionASPArr HA).
  Local Notation comp := (@arr_comp optionASPArr HA).
  Local Notation first := (@arr_first optionASPArr HA).
  Local Notation second := (@arr_second optionASPArr HA).
  Local Notation app := (@arr_app optionASPArr HA
    (@ArrowApply_optionArrT PureRelASPPairArr Arrow_PureRelASPPairArr
      ArrowChoice_PureRelASPPairArr ArrowApply_PureRelASPPairArr)).

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
    (@Arrow_optionArrT PureRelDSLPPairArr Arrow_PureRelDSLPPairArr ArrowChoice_PureRelDSLPPairArr).
  Local Notation pure := (@arr_pure optionDSLPArr HA).
  Local Notation comp := (@arr_comp optionDSLPArr HA).
  Local Notation first := (@arr_first optionDSLPArr HA).
  Local Notation second := (@arr_second optionDSLPArr HA).
  Local Notation app := (@arr_app optionDSLPArr HA
    (@ArrowApply_optionArrT PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
      ArrowChoice_PureRelDSLPPairArr ArrowApply_PureRelDSLPPairArr)).

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
  Local Notation HA := (@Arrow_stateArrT S PureRelASPPairArr Arrow_PureRelASPPairArr).
  Local Notation pure := (@arr_pure (stateArrT S PureRelASPPairArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S PureRelASPPairArr) HA).
  Local Notation first := (@arr_first (stateArrT S PureRelASPPairArr) HA).
  Local Notation second := (@arr_second (stateArrT S PureRelASPPairArr) HA).
  Local Notation app := (@arr_app (stateArrT S PureRelASPPairArr) HA
    (@ArrowApply_stateArrT S PureRelASPPairArr Arrow_PureRelASPPairArr ArrowApply_PureRelASPPairArr)).

  Lemma stateASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S PureRelASPPairArr) HA (A * B).
  Proof. exact (rel_state_app_unit ASP_rel_presentation S A B). Qed.

  Lemma stateASP_app_precompose {A B C} (g : stateArrT S PureRelASPPairArr A B) :
    comp (first (pure (fun f : stateArrT S PureRelASPPairArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_state_app_precompose ASP_rel_presentation S g). Qed.

  Lemma stateASP_app_postcompose {A B C} (h : stateArrT S PureRelASPPairArr B C) :
    comp (first (pure (fun f : stateArrT S PureRelASPPairArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_state_app_postcompose ASP_rel_presentation S h). Qed.
End StateASPCoherence.

Section StateDSLPCoherence.
  Variable S : Type.
  Local Notation HA := (@Arrow_stateArrT S PureRelDSLPPairArr Arrow_PureRelDSLPPairArr).
  Local Notation pure := (@arr_pure (stateArrT S PureRelDSLPPairArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S PureRelDSLPPairArr) HA).
  Local Notation first := (@arr_first (stateArrT S PureRelDSLPPairArr) HA).
  Local Notation second := (@arr_second (stateArrT S PureRelDSLPPairArr) HA).
  Local Notation app := (@arr_app (stateArrT S PureRelDSLPPairArr) HA
    (@ArrowApply_stateArrT S PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
      ArrowApply_PureRelDSLPPairArr)).

  Lemma stateDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S PureRelDSLPPairArr) HA (A * B).
  Proof. exact (rel_state_app_unit DSLP_rel_presentation S A B). Qed.

  Lemma stateDSLP_app_precompose {A B C} (g : stateArrT S PureRelDSLPPairArr A B) :
    comp (first (pure (fun f : stateArrT S PureRelDSLPPairArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (rel_state_app_precompose DSLP_rel_presentation S g). Qed.

  Lemma stateDSLP_app_postcompose {A B C} (h : stateArrT S PureRelDSLPPairArr B C) :
    comp (first (pure (fun f : stateArrT S PureRelDSLPPairArr A B => comp f h))) app =
    comp app h.
  Proof. exact (rel_state_app_postcompose DSLP_rel_presentation S h). Qed.
End StateDSLPCoherence.

Section StateOptionASPCoherence.
  Variable S : Type.
  Local Notation OA :=
    (@Arrow_optionArrT PureRelASPPairArr Arrow_PureRelASPPairArr ArrowChoice_PureRelASPPairArr).
  Local Notation HA := (@Arrow_stateArrT S optionASPArr OA).
  Local Notation pure := (@arr_pure (stateArrT S optionASPArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S optionASPArr) HA).
  Local Notation first := (@arr_first (stateArrT S optionASPArr) HA).
  Local Notation second := (@arr_second (stateArrT S optionASPArr) HA).
  Local Notation app := (@arr_app (stateArrT S optionASPArr) HA
    (@ArrowApply_stateArrT S optionASPArr OA
      (@ArrowApply_optionArrT PureRelASPPairArr Arrow_PureRelASPPairArr
        ArrowChoice_PureRelASPPairArr ArrowApply_PureRelASPPairArr))).

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
    (@Arrow_optionArrT PureRelDSLPPairArr Arrow_PureRelDSLPPairArr ArrowChoice_PureRelDSLPPairArr).
  Local Notation HA := (@Arrow_stateArrT S optionDSLPArr OA).
  Local Notation pure := (@arr_pure (stateArrT S optionDSLPArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S optionDSLPArr) HA).
  Local Notation first := (@arr_first (stateArrT S optionDSLPArr) HA).
  Local Notation second := (@arr_second (stateArrT S optionDSLPArr) HA).
  Local Notation app := (@arr_app (stateArrT S optionDSLPArr) HA
    (@ArrowApply_stateArrT S optionDSLPArr OA
      (@ArrowApply_optionArrT PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
        ArrowChoice_PureRelDSLPPairArr ArrowApply_PureRelDSLPPairArr))).

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
