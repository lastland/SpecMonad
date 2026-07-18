(** * Arrow laws for [Rel] and [optionRelArr].

    This file proves [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws],
    and [ArrowLoopLaws] for the relational arrow [Rel].  The
    [ArrowLaws] / [ArrowChoiceLaws] / [ArrowApplyLaws] for
    [optionRelArr] are inherited from the generic transformer laws in
    [Classes/OptionArrowT] applied to these. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From Incorrectness.Classes Require Import
  Arrow OptionArrowT.
From Hammer Require Import Tactics.
From Incorrectness Require Import Taxonomy.Rel.

(* ================================================================= *)
(** ** Arrow laws for [Rel]                                          *)
(* ================================================================= *)

(** Helper: [arr_second] simplifies for [Rel].  This is stated as a
    Leibniz equality (using [funext] + [propext] internally) so that
    plain [rewrite] works on it.  [X] is the "extra" (untouched) type. *)
Lemma arr_second_Rel {X A B} (f : Rel A B) :
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

Create HintDb Rel_ops.
#[local] Hint Unfold arr_id arr_comp arr_first arr_pure arr_loop
  arr_left arr_app assoc_prod unassoc_prod swap : Rel_ops.

Local Ltac unfold_Rel_full :=
  autounfold with Rel_ops; unfold Arrow_Rel; simpl;
  repeat match goal with [p : _ * _ |- _] => destruct p end;
  repeat match goal with
  | [H : context[let '(_, _) := ?p in _] |- _] => destruct p
  | [|- context[let '(_, _) := ?p in _]] => destruct p
  end.

(** After [intros a b] the goal [arrow_eq f g] (which unfolds to
    [forall a b, f a b <-> g a b] via [ArrowEq_Rel] / [Rel_eq]) is
    just [f a b <-> g a b]. *)

#[global]
Instance ArrowLaws_Rel : ArrowLaws Rel.
Proof.
  constructor; intros.
  1-4: intros a b; unfold_Rel_full; sauto limit: 200.
  - (* first_pure *)
    intros [? ?] [? ?]; unfold_Rel_full; sauto limit: 200.
  - (* first_comp *)
    intros [? ?] [? ?]; unfold_Rel_full. split.
    + intros [[b [Hf Hg]] Heq]. subst.
      exists (b, d0); simpl; eauto.
    + intros [[b0 d1] [H1 H2]]; simpl in *.
      destruct H1, H2; subst; split; [exists b0|]; eauto.
  - (* first_fst *)
    intros [? ?] ?; unfold_Rel_full. split.
    + intros [[b0 c0] [H1 H2]]; simpl in *.
      destruct H1; subst; exists a; eauto.
    + intros [a0 [? ?]]; subst. exists (b, c); simpl; eauto.
  - (* first_assoc *)
    intros [[? ?] ?] [? [? ?]]; unfold_Rel_full. split.
    + intros [[[? ?] ?] [H1 H2]]; simpl in *.
      destruct H1 as [[? ?] ?]; inversion H2; subst.
      eexists (a, (_, _)); simpl; eauto.
    + intros [[? [? ?]] [H1 H2]]; simpl in *.
      inversion H1; subst. destruct H2 as [? H2]; inversion H2; subst.
      eexists (_, _, _); simpl; eauto.
  - (* comp_proper *)
    intros f1 f2 Hf g1 g2 Hg a c.
    cbv [arrow_eq ArrowEq_Rel Rel_eq] in Hf, Hg.
    unfold_Rel_full. sauto limit: 200.
  - (* first_proper *)
    intros f1 f2 Hf [a c] [b c'].
    cbv [arrow_eq ArrowEq_Rel Rel_eq] in Hf.
    unfold_Rel_full. sauto limit: 200.
Qed.

#[global]
Instance ArrowChoiceLaws_Rel : ArrowChoiceLaws Rel.
Proof.
  constructor; intros.
  - (* left_pure *)
    intros [a|c] [b|c']; unfold_Rel_full;
    unfold sum_bimap; sauto limit: 200.
  - (* left_comp *)
    intros [a|d] [c|d']; unfold_Rel_full.
    + split.
      * intros [b [Hf Hg]]. exists (inl b); eauto.
      * intros [x [H1 H2]]; destruct x as [b|d0];
        [exists b; eauto | simpl in *; contradiction].
    + sauto limit: 200.
    + sauto limit: 200.
    + split.
      * intros Heq; subst; exists (inr d'); eauto.
      * intros [[b|d0] [H1 H2]]; simpl in *; [contradiction | congruence].
  - (* left_inl *)
    intros a [b|c]; unfold_Rel_full.
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
    intros [[a|c]|d] [b|[c'|d']]; unfold_Rel_full;
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
    intros c y; unfold_Rel_full. split.
    + intros [x [Hinr Hleft]]. subst x.
      destruct y as [b|c']; simpl in Hleft; [contradiction | f_equal; exact Hleft].
    + intros Heq. subst y. exists (inr c). simpl. auto.
  - (* left_natural *)
    intros x y.
    destruct x as [a0|c0]; destruct y as [b0|d0]; unfold_Rel_full;
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
    unfold_Rel_full; unfold sum_prod_dist; simpl.
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
    cbv [arrow_eq ArrowEq_Rel Rel_eq] in Hf; unfold_Rel_full;
    try tauto.
    apply Hf.
Qed.

#[global]
Instance ArrowApplyLaws_Rel : ArrowApplyLaws Rel.
Proof.
  constructor; intros.
  intros a b; unfold_Rel_full. sauto limit: 200.
Qed.

#[global]
Instance ArrowLoopLaws_Rel : ArrowLoopLaws Rel.
Proof.
  constructor; intros.
  - (* loop_left_tightening *)
    intros a b. unfold_Rel_full. split.
    + intros [c [[b0 c0] [[Hh Heq] Hf]]]. subst c0.
      exists b0; split; [exact Hh | exists c; exact Hf].
    + intros [b0 [Hh [c Hf]]].
      exists c; exists (b0, c); sauto limit: 200.
  - (* loop_right_tightening *)
    intros a c. unfold_Rel_full. split.
    + intros [d [[b0 d0] [Hf [Hg Heq]]]]. subst d0.
      exists b0; split; [exists d; exact Hf | exact Hg].
    + intros [b0 [[d Hf] Hg]].
      exists d; exists (b0, d); sauto limit: 200.
  - (* loop_sliding *)
    intros a b.
    rewrite !arr_second_Rel.
    unfold arr_loop, arr_comp, arr_pure, Arrow_Rel; simpl. split.
    + intros [c [[b0 c0] [Hf [Hk Heq]]]]. subst b0. subst c.
      exists c0. exists (a, k c0). sauto limit: 200.
    + intros [c [[a0 c0] [[Hk Heq] Hf]]]. subst a0.
      exists c0. exists (b, c). sauto limit: 200.
  - (* loop_vanishing *)
    intros a b.
    unfold arr_loop, arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Rel; simpl.
    split.
    + intros [c [d Hf]]. exists (c, d); exists ((a, c), d); split; [reflexivity|].
      exists ((b, c), d); sauto limit: 200.
    + intros [[c d] [p [Heq1 [q [Hf Heq2]]]]].
      inversion Heq1; subst.
      destruct q as [[? ?] ?]; simpl in Heq2; inversion Heq2; subst.
      exists c; exists d; exact Hf.
  - (* loop_superposing *)
    intros [c a0] [c' b0].
    rewrite arr_second_Rel.
    unfold arr_loop; cbn.
    unfold arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Rel, swap; cbn.
    split.
    + intros [[d Hf] Heq]. subst c'.
      exists d; exists (c, (a0, d)); split; [reflexivity|].
      exists (c, (b0, d)); split.
      * exists ((a0, d), c); split; [reflexivity|].
        exists ((b0, d), c); sauto limit: 200.
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
(** ** [optionRelArr] law instances via generic [optionArrT] laws    *)
(* ================================================================= *)

(** Because [Rel] already has [ArrowLaws], [ArrowChoiceLaws], and
    [ArrowApplyLaws] instances, [optionRelArr = optionArrT Rel]
    inherits the transformer laws from [Classes/OptionArrowT] without
    any custom proof.  These definitions are sanity checks that
    confirm typeclass resolution succeeds. *)

Definition ArrowLaws_optionRelArr : ArrowLaws optionRelArr := _.
Definition ArrowChoiceLaws_optionRelArr : ArrowChoiceLaws optionRelArr := _.
Definition ArrowApplyLaws_optionRelArr : ArrowApplyLaws optionRelArr := _.
