(** * Standard application coherence for property-only SP arrows.

    Relations are recovered from the transformers in [SPostArr].  Their
    normal forms establish the relational semantics of the five direct
    operations.  [RelArrowCoherence.RelArrowPresentation] packages these
    derived proofs so that the generic coherence theorems can be reused.
    It adds no invariant
    to SP values and stores no relation in either SP carrier.

    The public lemmas prove the three standard [Control.Arrow] application
    equations (GHC 9.12.2), with Leibniz equality, for both property-only
    carriers and their option, state, and state-over-option transformers. *)

From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import SPostArr.
From Incorrectness.Classes Require RelArrowCoherence.

(** Compatibility aliases retain the module-qualified API after moving
    recovered relations and presentation witnesses into the core law module. *)
Definition ASP_rel := @SPostArr.ASP_rel.
Arguments ASP_rel {A B} f a b.
Definition DSLP_rel := @SPostArr.DSLP_rel.
Arguments DSLP_rel {A B} f a b.
Definition DSLP_rel_of_representation := @SPostArr.DSLP_rel_of_representation.
Arguments DSLP_rel_of_representation {A B} f R HR a b.
Definition ASP_rel_ext := @SPostArr.ASP_rel_ext.
Arguments ASP_rel_ext {A B} f g _.
Definition DSLP_rel_ext := @SPostArr.DSLP_rel_ext.
Arguments DSLP_rel_ext {A B} f g _.
Definition DSLP_rel_pure := @SPostArr.DSLP_rel_pure.
Arguments DSLP_rel_pure {A B} h a b.
Definition DSLP_rel_comp := @SPostArr.DSLP_rel_comp.
Arguments DSLP_rel_comp {A B C} f g a c.
Definition DSLP_rel_first := @SPostArr.DSLP_rel_first.
Arguments DSLP_rel_first {A B C} f a c b d.
Definition DSLP_rel_left := @SPostArr.DSLP_rel_left.
Arguments DSLP_rel_left {A B C} f x y.
Definition DSLP_rel_app := @SPostArr.DSLP_rel_app.
Arguments DSLP_rel_app {A B} f a b.
Definition ASP_rel_pure := @SPostArr.ASP_rel_pure.
Arguments ASP_rel_pure {A B} h a b.
Definition ASP_rel_comp := @SPostArr.ASP_rel_comp.
Arguments ASP_rel_comp {A B C} f g a c.
Definition ASP_rel_first := @SPostArr.ASP_rel_first.
Arguments ASP_rel_first {A B C} f a c b d.
Definition ASP_rel_left := @SPostArr.ASP_rel_left.
Arguments ASP_rel_left {A B C} f x y.
Definition ASP_rel_app := @SPostArr.ASP_rel_app.
Arguments ASP_rel_app {A B} f a b.
Definition ASP_rel_presentation := SPostArr.ASP_rel_presentation.
Definition DSLP_rel_presentation := SPostArr.DSLP_rel_presentation.

(** ** Concrete coherence API

    Each carrier has [_app_unit], [_app_precompose], and [_app_postcompose].
    Explicit dictionaries select the property-only operations throughout. *)

Section ASPCoherence.
  Local Notation HA := SPostArr.Arrow_PureASPostArr.
  Local Notation pure := (@arr_pure SPostArr.PureASPostArr HA).
  Local Notation comp := (@arr_comp SPostArr.PureASPostArr HA).
  Local Notation first := (@arr_first SPostArr.PureASPostArr HA).
  Local Notation second := (@arr_second SPostArr.PureASPostArr HA).
  Local Notation app :=
    (@arr_app SPostArr.PureASPostArr HA SPostArr.ArrowApply_PureASPostArr).

  Lemma ASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id SPostArr.PureASPostArr HA (A * B).
  Proof. exact (RelArrowCoherence.rel_app_unit ASP_rel_presentation A B). Qed.

  Lemma ASP_app_precompose {A B C} (g : SPostArr.PureASPostArr A B) :
    comp (first (pure (fun f : SPostArr.PureASPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (RelArrowCoherence.rel_app_precompose ASP_rel_presentation g). Qed.

  Lemma ASP_app_postcompose {A B C} (h : SPostArr.PureASPostArr B C) :
    comp (first (pure (fun f : SPostArr.PureASPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (RelArrowCoherence.rel_app_postcompose ASP_rel_presentation h). Qed.
End ASPCoherence.

Section DSLPCoherence.
  Local Notation HA := SPostArr.Arrow_PureDSLPostArr.
  Local Notation pure := (@arr_pure SPostArr.PureDSLPostArr HA).
  Local Notation comp := (@arr_comp SPostArr.PureDSLPostArr HA).
  Local Notation first := (@arr_first SPostArr.PureDSLPostArr HA).
  Local Notation second := (@arr_second SPostArr.PureDSLPostArr HA).
  Local Notation app :=
    (@arr_app SPostArr.PureDSLPostArr HA SPostArr.ArrowApply_PureDSLPostArr).

  Lemma DSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id SPostArr.PureDSLPostArr HA (A * B).
  Proof. exact (RelArrowCoherence.rel_app_unit DSLP_rel_presentation A B). Qed.

  Lemma DSLP_app_precompose {A B C} (g : SPostArr.PureDSLPostArr A B) :
    comp (first (pure (fun f : SPostArr.PureDSLPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (RelArrowCoherence.rel_app_precompose DSLP_rel_presentation g). Qed.

  Lemma DSLP_app_postcompose {A B C} (h : SPostArr.PureDSLPostArr B C) :
    comp (first (pure (fun f : SPostArr.PureDSLPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (RelArrowCoherence.rel_app_postcompose DSLP_rel_presentation h). Qed.
End DSLPCoherence.

Section OptionASPCoherence.
  Local Notation HA := SPostArr.Arrow_optionASPArr.
  Local Notation pure := (@arr_pure SPostArr.optionASPArr HA).
  Local Notation comp := (@arr_comp SPostArr.optionASPArr HA).
  Local Notation first := (@arr_first SPostArr.optionASPArr HA).
  Local Notation second := (@arr_second SPostArr.optionASPArr HA).
  Local Notation app :=
    (@arr_app SPostArr.optionASPArr HA SPostArr.ArrowApply_optionASPArr).

  Lemma optionASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id SPostArr.optionASPArr HA (A * B).
  Proof. exact (RelArrowCoherence.rel_option_app_unit ASP_rel_presentation A B). Qed.

  Lemma optionASP_app_precompose {A B C} (g : SPostArr.optionASPArr A B) :
    comp (first (pure (fun f : SPostArr.optionASPArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (RelArrowCoherence.rel_option_app_precompose ASP_rel_presentation g). Qed.

  Lemma optionASP_app_postcompose {A B C} (h : SPostArr.optionASPArr B C) :
    comp (first (pure (fun f : SPostArr.optionASPArr A B => comp f h))) app =
    comp app h.
  Proof. exact (RelArrowCoherence.rel_option_app_postcompose ASP_rel_presentation h). Qed.
End OptionASPCoherence.

Section OptionDSLPCoherence.
  Local Notation HA := SPostArr.Arrow_optionDSLPArr.
  Local Notation pure := (@arr_pure SPostArr.optionDSLPArr HA).
  Local Notation comp := (@arr_comp SPostArr.optionDSLPArr HA).
  Local Notation first := (@arr_first SPostArr.optionDSLPArr HA).
  Local Notation second := (@arr_second SPostArr.optionDSLPArr HA).
  Local Notation app :=
    (@arr_app SPostArr.optionDSLPArr HA SPostArr.ArrowApply_optionDSLPArr).

  Lemma optionDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id SPostArr.optionDSLPArr HA (A * B).
  Proof. exact (RelArrowCoherence.rel_option_app_unit DSLP_rel_presentation A B). Qed.

  Lemma optionDSLP_app_precompose {A B C} (g : SPostArr.optionDSLPArr A B) :
    comp (first (pure (fun f : SPostArr.optionDSLPArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (RelArrowCoherence.rel_option_app_precompose DSLP_rel_presentation g). Qed.

  Lemma optionDSLP_app_postcompose {A B C} (h : SPostArr.optionDSLPArr B C) :
    comp (first (pure (fun f : SPostArr.optionDSLPArr A B => comp f h))) app =
    comp app h.
  Proof. exact (RelArrowCoherence.rel_option_app_postcompose DSLP_rel_presentation h). Qed.
End OptionDSLPCoherence.

Section StateASPCoherence.
  Variable S : Type.
  Local Notation HA :=
    (@Arrow_stateArrT S SPostArr.PureASPostArr SPostArr.Arrow_PureASPostArr).
  Local Notation pure := (@arr_pure (stateArrT S SPostArr.PureASPostArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S SPostArr.PureASPostArr) HA).
  Local Notation first := (@arr_first (stateArrT S SPostArr.PureASPostArr) HA).
  Local Notation second := (@arr_second (stateArrT S SPostArr.PureASPostArr) HA).
  Local Notation app := (@arr_app (stateArrT S SPostArr.PureASPostArr) HA
    (@ArrowApply_stateArrT S SPostArr.PureASPostArr
      SPostArr.Arrow_PureASPostArr SPostArr.ArrowApply_PureASPostArr)).

  Lemma stateASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S SPostArr.PureASPostArr) HA (A * B).
  Proof. exact (RelArrowCoherence.rel_state_app_unit ASP_rel_presentation S A B). Qed.

  Lemma stateASP_app_precompose {A B C} (g : stateArrT S SPostArr.PureASPostArr A B) :
    comp (first (pure (fun f : stateArrT S SPostArr.PureASPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (RelArrowCoherence.rel_state_app_precompose ASP_rel_presentation S g). Qed.

  Lemma stateASP_app_postcompose {A B C} (h : stateArrT S SPostArr.PureASPostArr B C) :
    comp (first (pure (fun f : stateArrT S SPostArr.PureASPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (RelArrowCoherence.rel_state_app_postcompose ASP_rel_presentation S h). Qed.
End StateASPCoherence.

Section StateDSLPCoherence.
  Variable S : Type.
  Local Notation HA :=
    (@Arrow_stateArrT S SPostArr.PureDSLPostArr SPostArr.Arrow_PureDSLPostArr).
  Local Notation pure := (@arr_pure (stateArrT S SPostArr.PureDSLPostArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S SPostArr.PureDSLPostArr) HA).
  Local Notation first := (@arr_first (stateArrT S SPostArr.PureDSLPostArr) HA).
  Local Notation second := (@arr_second (stateArrT S SPostArr.PureDSLPostArr) HA).
  Local Notation app := (@arr_app (stateArrT S SPostArr.PureDSLPostArr) HA
    (@ArrowApply_stateArrT S SPostArr.PureDSLPostArr
      SPostArr.Arrow_PureDSLPostArr SPostArr.ArrowApply_PureDSLPostArr)).

  Lemma stateDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S SPostArr.PureDSLPostArr) HA (A * B).
  Proof. exact (RelArrowCoherence.rel_state_app_unit DSLP_rel_presentation S A B). Qed.

  Lemma stateDSLP_app_precompose {A B C} (g : stateArrT S SPostArr.PureDSLPostArr A B) :
    comp (first (pure (fun f : stateArrT S SPostArr.PureDSLPostArr B C => comp g f))) app =
    comp (second g) app.
  Proof. exact (RelArrowCoherence.rel_state_app_precompose DSLP_rel_presentation S g). Qed.

  Lemma stateDSLP_app_postcompose {A B C} (h : stateArrT S SPostArr.PureDSLPostArr B C) :
    comp (first (pure (fun f : stateArrT S SPostArr.PureDSLPostArr A B => comp f h))) app =
    comp app h.
  Proof. exact (RelArrowCoherence.rel_state_app_postcompose DSLP_rel_presentation S h). Qed.
End StateDSLPCoherence.

Section StateOptionASPCoherence.
  Variable S : Type.
  Local Notation HA := (SPostArr.Arrow_stateOptASP S).
  Local Notation pure := (@arr_pure (stateArrT S SPostArr.optionASPArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S SPostArr.optionASPArr) HA).
  Local Notation first := (@arr_first (stateArrT S SPostArr.optionASPArr) HA).
  Local Notation second := (@arr_second (stateArrT S SPostArr.optionASPArr) HA).
  Local Notation app := (@arr_app (stateArrT S SPostArr.optionASPArr) HA
    (SPostArr.ArrowApply_stateOptASP S)).

  Lemma stateOptASP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S SPostArr.optionASPArr) HA (A * B).
  Proof.
    exact (RelArrowCoherence.rel_state_option_app_unit ASP_rel_presentation S A B).
  Qed.

  Lemma stateOptASP_app_precompose {A B C} (g : stateArrT S SPostArr.optionASPArr A B) :
    comp (first (pure (fun f : stateArrT S SPostArr.optionASPArr B C => comp g f))) app =
    comp (second g) app.
  Proof.
    exact (RelArrowCoherence.rel_state_option_app_precompose ASP_rel_presentation S g).
  Qed.

  Lemma stateOptASP_app_postcompose {A B C} (h : stateArrT S SPostArr.optionASPArr B C) :
    comp (first (pure (fun f : stateArrT S SPostArr.optionASPArr A B => comp f h))) app =
    comp app h.
  Proof.
    exact (RelArrowCoherence.rel_state_option_app_postcompose ASP_rel_presentation S h).
  Qed.
End StateOptionASPCoherence.

Section StateOptionDSLPCoherence.
  Variable S : Type.
  Local Notation HA := (SPostArr.Arrow_stateOptDSLP S).
  Local Notation pure := (@arr_pure (stateArrT S SPostArr.optionDSLPArr) HA).
  Local Notation comp := (@arr_comp (stateArrT S SPostArr.optionDSLPArr) HA).
  Local Notation first := (@arr_first (stateArrT S SPostArr.optionDSLPArr) HA).
  Local Notation second := (@arr_second (stateArrT S SPostArr.optionDSLPArr) HA).
  Local Notation app := (@arr_app (stateArrT S SPostArr.optionDSLPArr) HA
    (SPostArr.ArrowApply_stateOptDSLP S)).

  Lemma stateOptDSLP_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app =
    @arr_id (stateArrT S SPostArr.optionDSLPArr) HA (A * B).
  Proof.
    exact (RelArrowCoherence.rel_state_option_app_unit DSLP_rel_presentation S A B).
  Qed.

  Lemma stateOptDSLP_app_precompose {A B C} (g : stateArrT S SPostArr.optionDSLPArr A B) :
    comp (first (pure (fun f : stateArrT S SPostArr.optionDSLPArr B C => comp g f))) app =
    comp (second g) app.
  Proof.
    exact (RelArrowCoherence.rel_state_option_app_precompose DSLP_rel_presentation S g).
  Qed.

  Lemma stateOptDSLP_app_postcompose {A B C} (h : stateArrT S SPostArr.optionDSLPArr B C) :
    comp (first (pure (fun f : stateArrT S SPostArr.optionDSLPArr A B => comp f h))) app =
    comp app h.
  Proof.
    exact (RelArrowCoherence.rel_state_option_app_postcompose DSLP_rel_presentation S h).
  Qed.
End StateOptionDSLPCoherence.
