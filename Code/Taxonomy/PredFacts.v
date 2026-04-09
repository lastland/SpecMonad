(** * Laws for [Pred] and [optionPred].

    This file collects [Eq1Equivalence] and [MonadLawsE] for [Pred],
    the direct relational characterizations of [arr_comp] and
    [arr_first] for [optionPred], and the [ArrowLaws],
    [ArrowChoiceLaws], and [ArrowApplyLaws] instances. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import
  Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy Require Import ProgFacts.
From Incorrectness Require Import Taxonomy.Pred.

(* ================================================================= *)
(** ** [Pred A] monad laws                                            *)
(* ================================================================= *)

#[global]
Instance Eq1Equivalence_Pred {A}
  : @Eq1Equivalence (Pred A) _ Eq1_Pred.
Proof.
  constructor; repeat intro; unfold eq1, Eq1_Pred in *.
  - reflexivity.
  - symmetry. apply H.
  - etransitivity; [apply H | apply H0].
Qed.

#[global]
Instance MonadLawsE_Pred {A} : @MonadLawsE (Pred A) Eq1_Pred _.
Proof.
  constructor.
  - (* bind_ret_l *)
    intros B C f x a c.
    cbn. unfold bindPred, retPred. split.
    + intros [b [Heq Hk]]. subst. exact Hk.
    + intro Hk. exists x. split; [reflexivity | exact Hk].
  - (* bind_ret_r *)
    intros B x a b.
    cbn. unfold bindPred, retPred. split.
    + intros [b' [Hm Heq]]. subst. exact Hm.
    + intro Hm. exists b. split; [exact Hm | reflexivity].
  - (* bind_bind *)
    intros B C D x f g a d.
    cbn. unfold bindPred. split.
    + intros [c [[b [Hx Hf]] Hg]].
      exists b. split; [exact Hx | exists c; exact (conj Hf Hg)].
    + intros [b [Hx [c [Hf Hg]]]].
      exists c. split; [exists b; exact (conj Hx Hf) | exact Hg].
  - (* Proper_bind *)
    intros B C m1 m2 Hm k1 k2 Hk a c.
    cbn. unfold bindPred.
    unfold eq1, Eq1_Pred in Hm.
    split.
    + intros [b [Hm1 Hk1]].
      exists b. split; [apply Hm; exact Hm1 | apply (Hk b a c); exact Hk1].
    + intros [b [Hm2 Hk2]].
      exists b. split; [apply Hm; exact Hm2 | apply (Hk b a c); exact Hk2].
Qed.

(* ================================================================= *)
(** ** Direct relational characterizations for [optionPred]           *)
(* ================================================================= *)

(** Unfold the generic [arr_comp] for [Pred] into a direct relational
    form. *)
Lemma optionArrT_comp_Pred {A B C}
  (f : optionPred A B) (g : optionPred B C) :
  @arr_comp _ Arrow_optionArrT A B C f g =
  fun a oc => match oc with
    | Some c => exists b, f a (Some b) /\ g b (Some c)
    | None => f a None \/ exists b, f a (Some b) /\ g b None
  end.
Proof.
  apply optionPred_eq; intros a oc.
  unfold arr_comp at 1, Arrow_optionArrT, Arrow_Pred, ArrowChoice_Pred.
  cbn. unfold to_sum, collapse.
  destruct oc as [c|].
  - (* Some c *)
    split.
    + intros [ob [Hf [x [Hts [y [Hleft Hcoll]]]]]].
      destruct ob as [b|]; simpl in Hts; subst x;
      destruct y as [[c0|]|[]]; simpl in *;
      try destruct Hleft; try discriminate.
      injection Hcoll as ->. exists b. auto.
    + intros [b [Hf Hg]].
      exists (Some b). split; [exact Hf|].
      exists (inl b). split; [reflexivity|].
      exists (inl (Some c)). split; [exact Hg | reflexivity].
  - (* None *)
    split.
    + intros [ob [Hf [x [Hts [y [Hleft Hcoll]]]]]].
      destruct ob as [b|]; simpl in Hts; subst x;
      destruct y as [[c0|]|[]]; simpl in *;
      try destruct Hleft; try discriminate.
      * right. exists b. auto.
      * left. exact Hf.
    + intros [Hf | [b [Hf Hg]]].
      * exists None. split; [exact Hf|].
        exists (inr tt). split; [reflexivity|].
        exists (inr tt). split; [reflexivity | reflexivity].
      * exists (Some b). split; [exact Hf|].
        exists (inl b). split; [reflexivity|].
        exists (inl None). split; [exact Hg | reflexivity].
Qed.

(** Unfold the generic [arr_first] for [Pred]. *)
Lemma optionArrT_first_Pred {A B C}
  (f : optionPred A B) :
  @arr_first _ Arrow_optionArrT A B C f =
  fun p oq => let '(a, c) := p in
    match oq with
    | Some (b, c') => f a (Some b) /\ c = c'
    | None => f a None
    end.
Proof.
  apply optionPred_eq; intros [a c] oq.
  unfold arr_first at 1, Arrow_optionArrT, Arrow_Pred.
  cbn. unfold sequence_option.
  destruct oq as [[b c']|].
  - split.
    + intros [[ob d] [[Hf Hd] Heq]]. simpl in *.
      destruct ob; [injection Heq as -> -> | discriminate].
      exact (conj Hf Hd).
    + intros [Hf Hc]. subst. exists (Some b, c'). auto.
  - split.
    + intros [[ob d] [[Hf Hd] Heq]]. simpl in *.
      destruct ob; [discriminate | ]. subst. exact Hf.
    + intros Hf. exists (None, c). simpl. auto.
Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [optionPred]                                   *)
(* ================================================================= *)

#[global]
Instance ArrowLaws_optionPred : ArrowLaws optionPred.
Proof.
  constructor; intros.
  - (* comp_id_l *)
    apply optionPred_eq; intros a [c|]; rewrite optionArrT_comp_Pred;
    unfold arr_pure, Arrow_optionArrT; cbn.
    + split; [intros [b [Heq Hf]]; injection Heq as Heq; subst; exact Hf |
              intros Hf; exists a; eauto].
    + split; [intros [Habs | [b [Heq Hf]]]; [discriminate Habs | injection Heq as Heq; subst; exact Hf] |
              intros Hf; right; exists a; eauto].
  - (* comp_id_r *)
    apply optionPred_eq; intros a [c|]; rewrite optionArrT_comp_Pred;
    unfold arr_pure, Arrow_optionArrT; cbn.
    + split; [intros [b [Hf Heq]]; injection Heq as Heq; subst; exact Hf |
              intros Hf; exists c; eauto].
    + split; [intros [H | [b [Hf Habs]]]; [exact H | discriminate Habs] |
              intros Hf; left; exact Hf].
  - (* comp_assoc *)
    apply optionPred_eq; intros a [d|]; rewrite !optionArrT_comp_Pred.
    + split.
      * intros [c [[b [Hf Hg]] Hh]]. exists b; split; [exact Hf|]. exists c; eauto.
      * intros [b [Hf [c [Hg Hh]]]]. exists c; split; [exists b|]; eauto.
    + split.
      * intros [[Hf | [b [Hf Hg]]] | [c [[b [Hf Hg]] Hh]]].
        -- left. exact Hf.
        -- right. exists b; split; [exact Hf | left; exact Hg].
        -- right. exists b; split; [exact Hf | right; exists c; eauto].
      * intros [Hf | [b [Hf [Hg | [c [Hg Hh]]]]]].
        -- left. left. exact Hf.
        -- left. right. exists b; eauto.
        -- right. exists c; split; [exists b; eauto | exact Hh].
  - (* pure_comp *)
    apply optionPred_eq; intros a [c|]; rewrite optionArrT_comp_Pred;
    unfold arr_pure, Arrow_optionArrT; cbn.
    + split; [intros [b [Heq1 Heq2]]; injection Heq1 as Heq1; injection Heq2 as Heq2; subst; reflexivity |
              intros Heq; exists (f a); eauto].
    + split; [intros [H | [? [_ H]]]; discriminate H | intros H; discriminate H].
  - (* first_pure *)
    apply optionPred_eq; intros [a c] [[b c']|]; rewrite optionArrT_first_Pred;
    unfold arr_pure, Arrow_optionArrT; cbn.
    + split; [intros [Heq Hc]; injection Heq as Heq; subst; reflexivity |
              intro H; injection H as H1 H2; subst; eauto].
    + split; [intros H; discriminate H | intros H; discriminate H].
  - (* first_comp *)
    apply optionPred_eq; intros [a d] [[c d']|];
    rewrite optionArrT_first_Pred, !optionArrT_comp_Pred;
    rewrite !optionArrT_first_Pred.
    + split.
      * intros [[b [Hf Hg]] Heq]; subst d'.
        exists (b, d); simpl; eauto.
      * intros [[b0 d0] H]; simpl in H.
        destruct H as [[Hf Heq1] [Hg Heq2]]; subst.
        split; [exists b0; eauto | reflexivity].
    + split.
      * intros [Hf | [b [Hf Hg]]].
        -- left. exact Hf.
        -- right. exists (b, d); simpl; eauto.
      * intros [Hf | [[b d0] H]]; simpl in *.
        -- left. exact Hf.
        -- destruct H as [[Hf Heq] Hg]; subst.
           right. exists b; eauto.
  - (* first_fst *)
    apply optionPred_eq; intros [a c] [b|];
    rewrite !optionArrT_comp_Pred;
    rewrite !optionArrT_first_Pred;
    unfold arr_pure, Arrow_optionArrT; cbn.
    + split.
      * intros [[b0 c0] H]; simpl in H.
        destruct H as [[Hf Hc] Heq]; injection Heq as Heq; subst.
        exists a; eauto.
      * intros [a0 [Heq Hf]]; injection Heq as Heq; subst.
        exists (b, c); simpl; eauto.
    + split.
      * intros [Hf | [[b0 c0] H]]; simpl in *.
        -- right. exists a; eauto.
        -- destruct H as [_ Habs]; discriminate Habs.
      * intros [Habs | [a0 [Heq Hf]]].
        -- discriminate Habs.
        -- injection Heq as Heq; subst. left. exact Hf.
  - (* first_assoc *)
    apply optionPred_eq; intros [[a c] d] [ob|];
    rewrite !optionArrT_comp_Pred, !optionArrT_first_Pred;
    unfold arr_pure, Arrow_optionArrT, assoc_prod; cbn.
    + destruct ob as [b [c' d']]. split.
      * intros [[[b0 c0] d0] H]; simpl in H.
        destruct H as [[[Hf Hc] Hd] Heq].
        subst c0 d0. inversion Heq; subst.
        exists (a, (c', d')); simpl; split; [reflexivity|].
        split; [exact Hf | reflexivity].
      * intros [[a0 [c0 d0]] H]; simpl in H.
        destruct H as [Hassoc Hrest].
        inversion Hassoc; subst.
        destruct Hrest as [Hf Heq_cd].
        inversion Heq_cd; subst.
        eexists (_, _, _); simpl; eauto.
    + split.
      * intros [Hf | [[[b0 c0] d0] [_ Habs]]]; [| discriminate Habs].
        right. exists (a, (c, d)). split; [reflexivity | exact Hf].
      * intros [Habs | [[a0 [c0 d0]] [Heq Hf]]]; [discriminate Habs | ].
        inversion Heq; subst. left. exact Hf.
  - (* comp_proper *)
    unfold Proper, respectful; intros;
    cbv [arrow_eq ArrowEq_optionArrT ArrowEq_Pred] in *;
    subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful; intros;
    cbv [arrow_eq ArrowEq_optionArrT ArrowEq_Pred] in *;
    subst; reflexivity.
Qed.

(** [ArrowChoiceLaws_optionPred] and [ArrowApplyLaws_optionPred] are
    inherited automatically via the generic
    [ArrowChoiceLaws_optionArrT] / [ArrowApplyLaws_optionArrT]
    instances in [Classes/OptionArrowT]. *)

(** Sanity check: confirm these laws resolve for [optionPred]. *)
Definition ArrowChoiceLaws_optionPred : ArrowChoiceLaws optionPred := _.
Definition ArrowApplyLaws_optionPred : ArrowApplyLaws optionPred := _.

(* ================================================================= *)
(** ** Monad-view spec type sanity checks                             *)
(* ================================================================= *)

(** Sanity check: confirm [MonadLawsE] resolves through the
    transformer stack down to [MonadLawsE_Pred]. *)
Definition MonadLawsE__progPredM (S : Type)
  : @MonadLawsE (progPredM S) _ _ :=
  MonadLawsE_stateT S (optionT (Pred unit)).

Definition MonadLawsE__nditPredM (S : Type)
  : @MonadLawsE (nditPredM S) _ _ :=
  MonadLawsE_stateT S (optionT (optionT (Pred unit))).

