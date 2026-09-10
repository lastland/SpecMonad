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

From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import SPostArr.
From Incorrectness.Classes Require RelArrowCoherence.

(** ** Recovered relations and faithfulness *)

Definition ASP_rel {A B} (f : SPostArr.PureASPostArr A B) a b : Prop :=
  SPostArr.getASP f (eq a) b.

Definition DSLP_rel {A B} (f : SPostArr.PureDSLPostArr A B) a b : Prop :=
  forall Q, SPostArr.getDSLP f Q b -> Q a.

(** Any universal relational representation recovers its relation
    constructively: the forward direction chooses [Q := R (_, b)]. *)
Lemma DSLP_rel_of_representation {A B} (f : SPostArr.PureDSLPostArr A B)
  (R : A -> B -> Prop)
  (HR : forall Q b, SPostArr.getDSLP f Q b <-> forall a, R a b -> Q a) a b :
  DSLP_rel f a b <-> R a b.
Proof.
  unfold DSLP_rel. split.
  - intro H. apply (H (fun a' => R a' b)). apply HR. auto.
  - intros Hab Q HQ. exact (proj1 (HR Q b) HQ a Hab).
Qed.

Lemma ASP_rel_ext {A B} (f g : SPostArr.PureASPostArr A B) :
  (forall a b, ASP_rel f a b <-> ASP_rel g a b) -> f = g.
Proof.
  intro Hrel. apply SPostArr.PureASPostArr_eq. intros Q b.
  rewrite (SPostArr.ASP_normal_form f), (SPostArr.ASP_normal_form g).
  split; intros [a [HQ Hr]]; exists a; split.
  - exact HQ.
  - apply Hrel. exact Hr.
  - exact HQ.
  - apply Hrel. exact Hr.
Qed.

Lemma DSLP_rel_ext {A B} (f g : SPostArr.PureDSLPostArr A B) :
  (forall a b, DSLP_rel f a b <-> DSLP_rel g a b) -> f = g.
Proof.
  intro Hrel. apply SPostArr.PureDSLPostArr_eq. intros Q b.
  rewrite (SPostArr.DSLP_normal_form f), (SPostArr.DSLP_normal_form g).
  split; intros H a Hr; apply H; apply Hrel; exact Hr.
Qed.

(** ** Demonic relation semantics

    Each direct transformer is put into a universal relational normal
    form, then [DSLP_rel_of_representation] recovers that relation. *)

Lemma DSLP_rel_pure {A B} (h : A -> B) a b :
  DSLP_rel (SPostArr.pureDSLP h) a b <-> h a = b.
Proof.
  apply (DSLP_rel_of_representation (SPostArr.pureDSLP h) (fun a b => h a = b)).
  intros Q b'. apply SPostArr.pureDSLP_spec.
Qed.

Lemma DSLP_rel_comp {A B C}
  (f : SPostArr.PureDSLPostArr A B) (g : SPostArr.PureDSLPostArr B C) a c :
  DSLP_rel (SPostArr.compDSLP f g) a c <->
  exists b, DSLP_rel f a b /\ DSLP_rel g b c.
Proof.
  apply (DSLP_rel_of_representation (SPostArr.compDSLP f g)
    (fun a c => exists b, DSLP_rel f a b /\ DSLP_rel g b c)).
  intros Q c'. rewrite SPostArr.compDSLP_spec, (SPostArr.DSLP_normal_form g).
  split.
  - intros H a' [b [Hf Hg]]. exact (Hf Q (H b Hg)).
  - intros H b Hg. apply SPostArr.DSLP_normal_form. intros a' Hf.
    apply H. exists b. split; assumption.
Qed.

Lemma DSLP_rel_first {A B C} (f : SPostArr.PureDSLPostArr A B) a (c : C) b d :
  DSLP_rel (SPostArr.firstDSLP f) (a, c) (b, d) <-> DSLP_rel f a b /\ c = d.
Proof.
  apply (DSLP_rel_of_representation (SPostArr.firstDSLP f)
    (fun '(a, c) '(b, d) => DSLP_rel f a b /\ c = d))
    with (a := (a, c)) (b := (b, d)).
  intros Q [b' d']. rewrite SPostArr.firstDSLP_spec, (SPostArr.DSLP_normal_form f).
  split.
  - intros H [a' c'] [Hf Heq]. cbn in Heq. subst c'. exact (H a' Hf).
  - intros H a' Hf. apply (H (a', d')). split; [exact Hf | reflexivity].
Qed.

Lemma DSLP_rel_left {A B C} (f : SPostArr.PureDSLPostArr A B)
  (x : A + C) (y : B + C) :
  DSLP_rel (SPostArr.leftDSLP f) x y <->
  match x, y with
  | inl a, inl b => DSLP_rel f a b
  | inr c, inr d => c = d
  | _, _ => False
  end.
Proof.
  apply (DSLP_rel_of_representation (SPostArr.leftDSLP f)
    (fun x y => match x, y with
      | inl a, inl b => DSLP_rel f a b
      | inr c, inr d => c = d
      | _, _ => False
      end)) with (a := x) (b := y).
  intros Q [b|d]; rewrite SPostArr.leftDSLP_spec; cbn.
  - rewrite (SPostArr.DSLP_normal_form f). split.
    + intros H [a|c] Hr; [exact (H a Hr) | contradiction].
    + intros H a Hr. exact (H (inl a) Hr).
  - split.
    + intros HQ [a|c] Hr; [contradiction | subst c; exact HQ].
    + intro H. exact (H (inr d) eq_refl).
Qed.

Lemma DSLP_rel_app {A B} (f : SPostArr.PureDSLPostArr A B) a b :
  DSLP_rel SPostArr.appDSLP (f, a) b <-> DSLP_rel f a b.
Proof.
  apply (DSLP_rel_of_representation SPostArr.appDSLP
    (fun '(f, a) b => DSLP_rel f a b)) with (a := (f, a)) (b := b).
  intros Q b'. rewrite SPostArr.appDSLP_spec. split.
  - intros H [f' a'] Hr. exact (Hr (fun a => Q (f', a)) (H f')).
  - intros H f'. apply SPostArr.DSLP_normal_form. intros a' Hr.
    exact (H (f', a') Hr).
Qed.

(** ** Angelic relation semantics *)

Lemma ASP_rel_pure {A B} (h : A -> B) a b :
  ASP_rel (SPostArr.pureASP h) a b <-> h a = b.
Proof.
  unfold ASP_rel. rewrite SPostArr.pureASP_spec. split.
  - intros [a' [<- Hh]]. exact Hh.
  - intro Hh. exists a. split; [reflexivity | exact Hh].
Qed.

Lemma ASP_rel_comp {A B C}
  (f : SPostArr.PureASPostArr A B) (g : SPostArr.PureASPostArr B C) a c :
  ASP_rel (SPostArr.compASP f g) a c <->
  exists b, ASP_rel f a b /\ ASP_rel g b c.
Proof.
  unfold ASP_rel. rewrite SPostArr.compASP_spec, (SPostArr.ASP_normal_form g).
  reflexivity.
Qed.

Lemma ASP_rel_first {A B C} (f : SPostArr.PureASPostArr A B) a (c : C) b d :
  ASP_rel (SPostArr.firstASP f) (a, c) (b, d) <-> ASP_rel f a b /\ c = d.
Proof.
  unfold ASP_rel. rewrite SPostArr.firstASP_spec, (SPostArr.ASP_normal_form f).
  split.
  - intros [a' [Heq Hr]]. injection Heq as <- <-. split; [exact Hr | reflexivity].
  - intros [Hr ->]. exists a. split; [reflexivity | exact Hr].
Qed.

Lemma ASP_rel_left {A B C} (f : SPostArr.PureASPostArr A B)
  (x : A + C) (y : B + C) :
  ASP_rel (SPostArr.leftASP f) x y <->
  match x, y with
  | inl a, inl b => ASP_rel f a b
  | inr c, inr d => c = d
  | _, _ => False
  end.
Proof.
  unfold ASP_rel. destruct x as [a|c], y as [b|d];
    rewrite SPostArr.leftASP_spec; cbn.
  - rewrite (SPostArr.ASP_normal_form f). split.
    + intros [a' [Heq Hr]]. injection Heq as <-. exact Hr.
    + intro Hr. exists a. split; [reflexivity | exact Hr].
  - split; [intro H; discriminate H | contradiction].
  - rewrite (SPostArr.ASP_normal_form f). split.
    + intros [a [Heq _]]. discriminate Heq.
    + contradiction.
  - split.
    + intro H. injection H as H. exact H.
    + intros ->. reflexivity.
Qed.

Lemma ASP_rel_app {A B} (f : SPostArr.PureASPostArr A B) a b :
  ASP_rel SPostArr.appASP (f, a) b <-> ASP_rel f a b.
Proof.
  unfold ASP_rel. rewrite SPostArr.appASP_spec. split.
  - intros [f' H]. rewrite (SPostArr.ASP_normal_form f') in H.
    destruct H as [a' [Heq Hr]]. injection Heq as <- <-. exact Hr.
  - intro Hr. exists f. rewrite (SPostArr.ASP_normal_form f).
    exists a. split; [reflexivity | exact Hr].
Qed.

(** ** Derived proof packages for the existing property-only carriers *)

Definition ASP_rel_presentation :
  RelArrowCoherence.RelArrowPresentation SPostArr.PureASPostArr
    SPostArr.Arrow_PureASPostArr SPostArr.ArrowChoice_PureASPostArr
    SPostArr.ArrowApply_PureASPostArr := {|
  RelArrowCoherence.present_rel := @ASP_rel;
  RelArrowCoherence.present_ext := @ASP_rel_ext;
  RelArrowCoherence.present_pure := @ASP_rel_pure;
  RelArrowCoherence.present_comp := @ASP_rel_comp;
  RelArrowCoherence.present_first := @ASP_rel_first;
  RelArrowCoherence.present_left := @ASP_rel_left;
  RelArrowCoherence.present_app := @ASP_rel_app
|}.

Definition DSLP_rel_presentation :
  RelArrowCoherence.RelArrowPresentation SPostArr.PureDSLPostArr
    SPostArr.Arrow_PureDSLPostArr SPostArr.ArrowChoice_PureDSLPostArr
    SPostArr.ArrowApply_PureDSLPostArr := {|
  RelArrowCoherence.present_rel := @DSLP_rel;
  RelArrowCoherence.present_ext := @DSLP_rel_ext;
  RelArrowCoherence.present_pure := @DSLP_rel_pure;
  RelArrowCoherence.present_comp := @DSLP_rel_comp;
  RelArrowCoherence.present_first := @DSLP_rel_first;
  RelArrowCoherence.present_left := @DSLP_rel_left;
  RelArrowCoherence.present_app := @DSLP_rel_app
|}.

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
