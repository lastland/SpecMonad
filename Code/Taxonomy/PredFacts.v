(** * Laws for [Pred] and [optionPred].

    This file proves [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws],
    and [ArrowLoopLaws] for the relational arrow [Pred], plus
    [Eq1Equivalence] and [MonadLawsE] for the second-argument monad
    instance on [Pred A].  The [ArrowLaws] / [ArrowChoiceLaws] /
    [ArrowApplyLaws] for [optionPred] are inherited from the generic
    transformer laws in [Classes/OptionArrowT] applied to these. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import
  Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy Require Import ProgFacts.
From Incorrectness Require Import Taxonomy.Pred.

(* ================================================================= *)
(** ** Arrow laws for [Pred]                                          *)
(* ================================================================= *)

(** Helper: [arr_second] simplifies for [Pred].  This is stated as a
    Leibniz equality (using [funext] + [propext] internally) so that
    plain [rewrite] works on it.  [X] is the "extra" (untouched) type. *)
Lemma arr_second_Pred {X A B} (f : Pred A B) :
  @arr_second _ _ A B X f =
  fun (p : X * A) (q : X * B) =>
    let '(c, a) := p in let '(c', b) := q in f a b /\ c = c'.
Proof.
  extensionality p. extensionality q.
  apply propositional_extensionality.
  destruct p as [c a], q as [c' b].
  unfold arr_second, arr_comp, arr_first, arr_pure, swap; cbn.
  split.
  - intros [[a0 c0] [Heq [[b1 c1] [Hf Hswap]]]].
    inversion Heq; subst. simpl in *. inversion Hswap; subst. exact Hf.
  - intros [Hf Heq]. subst.
    exists (a, c'). split; [reflexivity|].
    exists (b, c'). simpl. split; [exact (conj Hf eq_refl)|reflexivity].
Qed.

Create HintDb Pred_ops.
#[local] Hint Unfold arr_id arr_comp arr_first arr_pure arr_loop
  arr_left arr_app assoc_prod unassoc_prod swap : Pred_ops.

Local Ltac unfold_Pred_full :=
  autounfold with Pred_ops; unfold Arrow_Pred; simpl;
  repeat match goal with [p : _ * _ |- _] => destruct p end;
  repeat match goal with
  | [H : context[let '(_, _) := ?p in _] |- _] => destruct p
  | [|- context[let '(_, _) := ?p in _]] => destruct p
  end.

(** After [intros a b] the goal [arrow_eq f g] (which unfolds to
    [forall a b, f a b <-> g a b] via [ArrowEq_Pred] / [Pred_eq]) is
    just [f a b <-> g a b]. *)

#[global]
Instance ArrowLaws_Pred : ArrowLaws Pred.
Proof.
  constructor; intros.
  1-4: intros a b; unfold_Pred_full;
       firstorder (subst; eauto; try congruence).
  - (* first_pure *)
    intros [? ?] [? ?]; unfold_Pred_full; firstorder congruence.
  - (* first_comp *)
    intros [? ?] [? ?]; unfold_Pred_full.
    split.
    + intros [[b [Hf Hg]] Heq]. subst.
      exists (b, d0); simpl; eauto.
    + intros [[b0 d1] [H1 H2]]; simpl in *.
      destruct H1, H2; subst; split; [exists b0|]; eauto.
  - (* first_fst *)
    intros [? ?] ?; unfold_Pred_full.
    split.
    + intros [[b0 c0] [H1 H2]]; simpl in *.
      destruct H1; subst; exists a; eauto.
    + intros [a0 [? ?]]; subst. exists (b, c); simpl; eauto.
  - (* first_assoc *)
    intros [[? ?] ?] [? [? ?]]; unfold_Pred_full.
    split.
    + intros [[[? ?] ?] [H1 H2]]; simpl in *.
      destruct H1 as [[? ?] ?]; inversion H2; subst.
      eexists (a, (_, _)); simpl; eauto.
    + intros [[? [? ?]] [H1 H2]]; simpl in *.
      inversion H1; subst. destruct H2 as [? H2]; inversion H2; subst.
      eexists (_, _, _); simpl; eauto.
  - (* comp_proper *)
    intros f1 f2 Hf g1 g2 Hg a c.
    cbv [arrow_eq ArrowEq_Pred Pred_eq] in Hf, Hg.
    unfold_Pred_full.
    split; intros [b [H1 H2]]; exists b;
      split; [apply Hf; exact H1 | apply Hg; exact H2 |
              apply Hf; exact H1 | apply Hg; exact H2].
  - (* first_proper *)
    intros f1 f2 Hf [a c] [b c'].
    cbv [arrow_eq ArrowEq_Pred Pred_eq] in Hf.
    unfold_Pred_full.
    split; intros [H1 H2]; split; try exact H2;
      [apply Hf; exact H1 | apply Hf; exact H1].
Qed.

#[global]
Instance ArrowChoiceLaws_Pred : ArrowChoiceLaws Pred.
Proof.
  constructor; intros.
  - (* left_pure *)
    intros [a|c] [b|c']; unfold_Pred_full;
    unfold sum_bimap; firstorder congruence.
  - (* left_comp *)
    intros [a|d] [c|d']; unfold_Pred_full.
    + split.
      * intros [b [Hf Hg]]. exists (inl b); eauto.
      * intros [x [H1 H2]]; destruct x as [b|d0];
        [exists b; eauto | simpl in *; contradiction].
    + split; [tauto | intros [x Hx]; destruct x; simpl in *; tauto].
    + split; [tauto | intros [x Hx]; destruct x; simpl in *; tauto].
    + split.
      * intros Heq; subst; exists (inr d'); eauto.
      * intros [[b|d0] [H1 H2]]; simpl in *; [contradiction | congruence].
  - (* left_inl *)
    intros a [b|c]; unfold_Pred_full.
    + split.
      * intros [b0 [Hf Heq]]; injection Heq as ->;
        exists (inl a); eauto.
      * intros [[a0|c0] [Heq Hf]]; [injection Heq as ->; exists b; eauto |
        simpl in *; destruct Hf].
    + split.
      * intros [b0 [Hf Heq]]; discriminate Heq.
      * intros [[a0|c0] [Heq Hf]]; [injection Heq as ->; simpl in *; destruct Hf |
        discriminate Heq].
  - (* left_assoc *)
    intros [[a|c]|d] [b|[c'|d']]; unfold_Pred_full;
    unfold assoc_sum; (split; intro H; destruct H as [x [H1 H2]];
      (destruct x as [[?|?]|?] || destruct x as [?|[?|?]]);
      simpl in *; try contradiction; try discriminate; subst;
      repeat match goal with
      | [H0 : inl _ = inl _ |- _] => injection H0; intros; subst; clear H0
      | [H0 : inr _ = inr _ |- _] => injection H0; intros; subst; clear H0
      end).
    all: first [ exists (inl a) | exists (inl (inl b))
                | exists (inr (inl c')) | exists (inl (inr c'))
                | exists (inr (inr d')) | exists (inr d') ]; eauto.
  - (* left_inr *)
    intros c y; unfold_Pred_full.
    split.
    + intros [x [Hinr Hleft]]. subst x.
      destruct y as [b|c']; simpl in Hleft; [contradiction | f_equal; exact Hleft].
    + intros Heq. subst y. exists (inr c). simpl. auto.
  - (* left_natural *)
    intros x y.
    destruct x as [a0|c0]; destruct y as [b0|d0]; unfold_Pred_full;
    unfold sum_bimap; simpl.
    all: split; intros [z [H1 H2]]; destruct z; simpl in *;
         try contradiction; try discriminate.
    all: repeat match goal with
         | [H : inl _ = inl _ |- _] => injection H; clear H; intros; subst
         | [H : inr _ = inr _ |- _] => injection H; clear H; intros; subst
         end.
    1-2: eexists (inl _); simpl; eauto.
    1-2: eexists (inr _); simpl; eauto.
  - (* first_left_dist *)
    intros [[a0|c0] d0] [[b0 d1]|[c1 d1]];
    unfold_Pred_full; unfold sum_prod_dist; simpl.
    all: split; intro H.
    all: repeat match goal with
      | [H : exists _, _ |- _] => destruct H
      | [H : _ /\ _ |- _] => destruct H
      | [H : (_ + _)%type |- _] => destruct H
      | [H : (_ * _)%type |- _] => destruct H
      | [p : (_ + _)%type |- _] => destruct p
      end; simpl in *;
      try contradiction; try discriminate;
      repeat match goal with
      | [H : inl _ = inl _ |- _] => injection H; clear H; intros; subst
      | [H : inr _ = inr _ |- _] => injection H; clear H; intros; subst
      | [H : (_, _) = (_, _) |- _] => injection H; clear H; intros; subst
      end.
    all: try (eexists (inl (_, _)); simpl; split; [reflexivity |]; eexists (_, _); simpl; eauto; fail).
    all: try (eexists (inr (_, _)); simpl; split; [reflexivity |]; eexists (_, _); simpl; eauto; fail).
    all: try (eexists (inl _, _); simpl; split; [eexists (inl _); simpl; eauto |]; eauto; fail).
    all: try (eexists (inr _, _); simpl; split; [eexists (inr _); simpl; eauto |]; eauto; fail).
    -- exists (inl (a0, d1)). auto.
    -- exists (inl b0, d1). simpl. auto.
    -- exists (inr (c1, d1)). auto.
    -- exists (inr c1, d1). simpl. auto.
  - (* left_proper *)
    intros f1 f2 Hf [a|c] [b|c'];
    cbv [arrow_eq ArrowEq_Pred Pred_eq] in Hf; unfold_Pred_full;
    try tauto.
    apply Hf.
Qed.

#[global]
Instance ArrowApplyLaws_Pred : ArrowApplyLaws Pred.
Proof.
  constructor; intros.
  intros a b; unfold_Pred_full.
  split.
  - intros [[g a'] [Heq Happ]]. inversion Heq; subst. exact Happ.
  - intros Hf. exists (f, a). exact (conj eq_refl Hf).
Qed.

#[global]
Instance ArrowLoopLaws_Pred : ArrowLoopLaws Pred.
Proof.
  constructor; intros.
  - (* loop_left_tightening *)
    intros a b. unfold_Pred_full. split.
    + intros [c [[b0 c0] [[Hh Heq] Hf]]]. subst c0.
      exists b0; split; [exact Hh | exists c; exact Hf].
    + intros [b0 [Hh [c Hf]]].
      exists c; exists (b0, c); split; [split; [exact Hh | reflexivity] | exact Hf].
  - (* loop_right_tightening *)
    intros a c. unfold_Pred_full. split.
    + intros [d [[b0 d0] [Hf [Hg Heq]]]]. subst d0.
      exists b0; split; [exists d; exact Hf | exact Hg].
    + intros [b0 [[d Hf] Hg]].
      exists d; exists (b0, d); split; [exact Hf | split; [exact Hg | reflexivity]].
  - (* loop_sliding *)
    intros a b.
    rewrite !arr_second_Pred.
    unfold arr_loop, arr_comp, arr_pure, Arrow_Pred; simpl. split.
    + intros [c [[b0 c0] [Hf [Hk Heq]]]]. subst b0. subst c.
      exists c0. exists (a, k c0). split; [split; reflexivity | exact Hf].
    + intros [c [[a0 c0] [[Hk Heq] Hf]]]. subst a0.
      exists c0. exists (b, c). split; [exact Hf | split; [exact Hk | reflexivity]].
  - (* loop_vanishing *)
    intros a b.
    unfold arr_loop, arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Pred; simpl.
    split.
    + intros [c [d Hf]]. exists (c, d); exists ((a, c), d); split; [reflexivity|].
      exists ((b, c), d); split; [exact Hf | reflexivity].
    + intros [[c d] [p [Heq1 [q [Hf Heq2]]]]].
      inversion Heq1; subst.
      destruct q as [[? ?] ?]; simpl in Heq2; inversion Heq2; subst.
      exists c; exists d; exact Hf.
  - (* loop_superposing *)
    intros [c a0] [c' b0].
    rewrite arr_second_Pred.
    unfold arr_loop; cbn.
    unfold arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Pred, swap; cbn.
    split.
    + intros [[d Hf] Heq]. subst c'.
      exists d; exists (c, (a0, d)); split; [reflexivity|].
      exists (c, (b0, d)); split.
      * exists ((a0, d), c); split; [reflexivity|].
        exists ((b0, d), c); split; [split; [exact Hf | reflexivity] | reflexivity].
      * reflexivity.
    + intros [d [p [Heq1 [q [Hmid Heq2]]]]].
      inversion Heq1; subst.
      destruct Hmid as [r [Hr [s [Hfs Hs]]]].
      destruct r as [[? ?] ?]; simpl in Hr; inversion Hr; subst.
      destruct s as [[? ?] ?]; simpl in *.
      destruct Hfs as [Hf Hc]. subst.
      inversion Heq2; subst.
      split; [eexists; exact Hf | reflexivity].
Qed.

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
(** ** [optionPred] law instances via generic [optionArrT] laws       *)
(* ================================================================= *)

(** Because [Pred] already has [ArrowLaws], [ArrowChoiceLaws], and
    [ArrowApplyLaws] instances, [optionPred = optionArrT Pred]
    inherits the transformer laws from [Classes/OptionArrowT] without
    any custom proof.  These definitions are sanity checks that
    confirm typeclass resolution succeeds. *)

Definition ArrowLaws_optionPred : ArrowLaws optionPred := _.
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
