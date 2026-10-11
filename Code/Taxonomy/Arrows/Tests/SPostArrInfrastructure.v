(** * Infrastructure regression for the fundamental SP arrow interface.

    Standalone checks that [SPostArr.v] alone supports downstream
    clients, with no BaseSpecMonads import: the four canonical law
    packages resolve; the moved DSP/ASLP binary stacks, relation
    constructors, and explicit dictionaries are available; split DSP
    composition is distinguished from naive transformer composition on a
    concrete reachability example; and the state-option bind semantics
    of the moved DSP stack at a non-unit input follows from the generic
    [RelArrowCoherence] normalization at the pinned canonical
    dictionaries. *)

From Incorrectness.Lib.Arrow Require
  Import Arrow ArrowMonad OptionArrowT StateArrowT RelArrowCoherence.
From Incorrectness.SP Require Import SPostArr.

(** ** Canonical law packages resolve through the fundamental interface *)

Definition asp_laws_resolved : ArrowLaws ASPArr := _.
Definition asp_choice_laws_resolved : ArrowChoiceLaws ASPArr := _.
Definition asp_apply_laws_resolved : ArrowApplyLaws ASPArr := _.

Definition dslp_laws_resolved : ArrowLaws DSLPArr := _.
Definition dslp_choice_laws_resolved : ArrowChoiceLaws DSLPArr := _.
Definition dslp_apply_laws_resolved : ArrowApplyLaws DSLPArr := _.

Definition dsp_laws_resolved : ArrowLaws DSPArr := _.
Definition dsp_choice_laws_resolved : ArrowChoiceLaws DSPArr := _.
Definition dsp_apply_laws_resolved : ArrowApplyLaws DSPArr := _.

Definition aslp_laws_resolved : ArrowLaws ASLPArr := _.
Definition aslp_choice_laws_resolved : ArrowChoiceLaws ASLPArr := _.
Definition aslp_apply_laws_resolved : ArrowApplyLaws ASLPArr := _.

(** The compatibility law packages remain transparent copies of the
    canonical ones, so both spellings denote one dictionary. *)
Example asp_compat_laws_identity :
  ArrowLaws_PureASPostArr = ArrowLaws_ASPArr.
Proof. reflexivity. Qed.

Example dslp_compat_apply_laws_identity :
  ArrowApplyLaws_PureDSLPostArr = ArrowApplyLaws_DSLPArr.
Proof. reflexivity. Qed.

(** ** Moved DSP/ASLP binary stacks and constructors are available *)

Definition dsp_stexc_apply_laws_resolved : ArrowApplyLaws (DSPStExcArr bool) :=
  ArrowApplyLaws_DSPStExcArr bool.
Definition aslp_st_laws_resolved : ArrowLaws (ASLPStArr bool) :=
  ArrowLaws_ASLPStArr bool.
Definition aslp_opt_apply_resolved : ArrowApply optASLP := ArrowApply_optASLP.

(** The moved state-option DSP application dictionary is exactly the
    one the generic state normalization below is instantiated with. *)
Example dsp_stexc_apply_dictionary_shape :
  ArrowApply_DSPStExcArr bool =
  @ArrowApply_stateArrT bool (optionArrT DSPArr)
    (@Arrow_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr)
    (@ArrowApply_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr
       ArrowApply_DSPArr).
Proof. reflexivity. Qed.

(** ** Split DSP composition is not transformer composition

    [R_ex] relates only [(true, true)], and [T_ex] accepts both
    predecessors.  Composing by split-operate-conjoin first makes the
    recovered relation the composite [S_ex], which at [tt] holds
    exactly for [x = true], so the composed arrow accepts the singleton
    [eq true].  Feeding the transformer of [f_ex] to [g_ex] directly
    instead forces [g_ex]'s demonic conjunct to demand the predicate at
    [false] too -- an intermediate the composite never reaches. *)

Definition R_ex : bool -> bool -> Prop := fun x y => x = true /\ y = true.
Definition T_ex : bool -> unit -> Prop := fun _ _ => True.
Definition S_ex : bool -> unit -> Prop :=
  fun x c => exists b, R_ex x b /\ T_ex b c.

Definition f_ex : DSPArr bool bool := dspOfRelArr R_ex.
Definition g_ex : DSPArr bool unit := dspOfRelArr T_ex.

Lemma dspRel_f_ex : forall x y, dspRel f_ex x y <-> R_ex x y.
Proof. exact (dspRel_ofRelArr R_ex). Qed.

Lemma dspRel_g_ex : forall x y, dspRel g_ex x y <-> T_ex x y.
Proof. exact (dspRel_ofRelArr T_ex). Qed.

(** The composed arrow's recovered relation is the composite of the two
    recovered relations, by the public DSP composition contract. *)
Lemma dspRel_comp_ex : forall x c, dspRel (arr_comp f_ex g_ex) x c <-> S_ex x c.
Proof.
  intros x c. split.
  - intro H. apply (proj1 (dspRel_comp f_ex g_ex x c)) in H.
    destruct H as [b [Hf Hg]].
    exists b. split;
      [ apply (proj1 (dspRel_f_ex x b)); exact Hf
      | apply (proj1 (dspRel_g_ex b c)); exact Hg ].
  - intros [b [Hf Hg]].
    apply (proj2 (dspRel_comp f_ex g_ex x c)).
    change (exists b, dspRel f_ex x b /\ dspRel g_ex b c).
    exists b. split;
      [ apply (proj2 (dspRel_f_ex x b)); exact Hf
      | apply (proj2 (dspRel_g_ex b c)); exact Hg ].
Qed.

(** The actual composed arrow accepts the singleton precondition: only
    [x = true] reaches [tt] through the composite. *)
Example dsp_split_compose_accepts : getDSP (arr_comp f_ex g_ex) (eq true) tt.
Proof.
  rewrite (dspRel_spec (arr_comp f_ex g_ex) (eq true) tt).
  rewrite (RelSPostArr.dspOf_cong (dspRel (arr_comp f_ex g_ex)) S_ex dspRel_comp_ex
             (eq true) tt).
  change ((exists x, eq true x /\ S_ex x tt)
          /\ (forall x, S_ex x tt -> eq true x)).
  unfold S_ex, R_ex, T_ex.
  split.
  - exists true. split; [ reflexivity | ].
    exists true. split; [ split; reflexivity | exact I ].
  - intros x [b [[Hx _] _]]. symmetry. exact Hx.
Qed.

(** Naive transformer composition rejects it: [g_ex]'s demonic conjunct
    quantifies over the unreachable intermediate [false]. *)
Example dsp_naive_transformer_comp_rejects :
  ~ getDSP g_ex (getDSP f_ex (eq true)) tt.
Proof.
  intro H.
  rewrite (dspRel_spec g_ex (getDSP f_ex (eq true)) tt) in H.
  rewrite (RelSPostArr.dspOf_cong (dspRel g_ex) T_ex dspRel_g_ex
             (getDSP f_ex (eq true)) tt) in H.
  change ((exists x, getDSP f_ex (eq true) x /\ T_ex x tt)
          /\ (forall x, T_ex x tt -> getDSP f_ex (eq true) x)) in H.
  destruct H as [_ Hall].
  pose proof (Hall false I) as Hfalse.
  rewrite (dspRel_spec f_ex (eq true) false) in Hfalse.
  rewrite (RelSPostArr.dspOf_cong (dspRel f_ex) R_ex dspRel_f_ex (eq true) false)
    in Hfalse.
  change ((exists x, eq true x /\ R_ex x false)
          /\ (forall x, R_ex x false -> eq true x)) in Hfalse.
  destruct Hfalse as [[x [_ Hr]] _]. unfold R_ex in Hr.
  destruct Hr as [_ Hbad]. discriminate Hbad.
Qed.

(** ** State-option bind semantics for the moved DSP stack at a non-unit
       input

    The dictionaries are pinned explicitly to the canonical DSP
    instances; the equation itself is the generic [relE_bind]
    normalization specialized through them, so the moved binary stack
    carries its bind semantics without any monad import. *)

Lemma dsp_stateOption_bind_nonunit {A B}
    (m : stateArrT bool (optionArrT DSPArr) bool A)
    (k : A -> stateArrT bool (optionArrT DSPArr) bool B)
    (i s : bool) (o : option (B * bool)) :
  dspRel (@bind_arrow (stateArrT bool (optionArrT DSPArr))
            (@Arrow_stateArrT bool (optionArrT DSPArr)
               (@Arrow_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr))
            (@ArrowApply_stateArrT bool (optionArrT DSPArr)
               (@Arrow_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr)
               (@ArrowApply_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr
                  ArrowApply_DSPArr))
            bool A B m k) (i, s) o <->
  exists o1, dspRel m (i, s) o1 /\
    match o1 with
    | Some (a, s') => dspRel (k a) (i, s') o
    | None => o = None
    end.
Proof.
  exact (@relE_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr RelArrow_DSPArr
           RelArrowApply_DSPArr ArrowChoice_DSPArr RelArrowChoice_DSPArr
           bool bool A B m k i s o).
Qed.

(** ** The ASLP constructor reads its relation back through public facts *)

Definition aslp_ex : ASLPArr bool unit := aslpOfRelArr (fun _ _ => True).

Example aslp_ex_accepts_top : getASLP aslp_ex (fun _ => True) tt.
Proof.
  apply (proj2 (aslpRel_spec aslp_ex (fun _ => True) tt)).
  rewrite (RelSPostArr.aslpOf_cong (aslpRel aslp_ex) (fun _ _ => True)
             (aslpRel_ofRelArr (fun _ _ => True)) (fun _ => True) tt).
  change ((exists x : bool, True /\ True) \/ (forall x : bool, True -> True)).
  left. exists true. split; exact I.
Qed.
