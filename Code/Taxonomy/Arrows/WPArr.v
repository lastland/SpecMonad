(** * The raw weakest-precondition arrow [WPArr].

    [WPArr A B = A -> WPureT B = A -> (B -> Prop) -> Prop] uses the
    unrestricted carrier from [BaseSpecMonads/WPureMonad.v], not its
    monotone subset [WPure].  Composition passes a continuation backward:

      [arr_comp f g a Q = f a (fun b => g b Q)].

    This file defines [WPArr_le], the arrow operations, and their
    [ArrowLaws], [ArrowChoiceLaws], and [ArrowApplyLaws] instances.
    Some equations hold by conversion; product and sum cases also use
    functional extensionality.  The generic [Monad_Arrow] construction
    supplies the fixed-input monad; concrete checks live in
    [Tests/ArrowMonadInstances.v].

    [arrow_eq] is Leibniz equality, unlike [WPure]'s pointwise iff.
    The raw carrier does not bundle a proof that a transformer respects
    pointwise-equivalent continuations. *)

From Coq Require Import RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.

(* ================================================================= *)
(** ** Type definition and refinement order                           *)
(* ================================================================= *)

Definition WPArr (A B : Type) : Type := A -> WPureT B.

(** DM4all refinement order (§3.1): reverse pointwise implication.
    [w1 ≤ w2] iff [w2 a Q → w1 a Q] for all [a], [Q].  A weaker
    precondition demand is lower in this order. *)
Definition WPArr_le {A B} (w1 w2 : WPArr A B) : Prop :=
  forall a Q, w2 a Q -> w1 a Q.

#[global]
Instance WPArr_le_PreOrder {A B} : PreOrder (@WPArr_le A B).
Proof. constructor; cbv; auto. Qed.

#[global]
Instance ArrowEq_WPArr : ArrowEq WPArr := {
  arrow_eq := fun A B => @eq (WPArr A B)
}.

#[global]
Instance Arrow_WPArr : Arrow WPArr := {
  arr_pure := fun A B f => fun a Q => Q (f a) ;
  arr_comp := fun A B C f g => fun a Q => f a (fun b => g b Q) ;
  arr_first := fun A B C f =>
    fun p Q => let '(a, c) := p in f a (fun b => Q (b, c))
}.

#[global]
Instance ArrowChoice_WPArr : ArrowChoice WPArr := {
  arr_left := fun A B C f =>
    fun x Q =>
      match x with
      | inl a => f a (fun b => Q (inl b))
      | inr c => Q (inr c)
      end
}.

#[global]
Instance ArrowApply_WPArr : ArrowApply WPArr := {
  arr_app := fun A B =>
    fun p Q => let '(f, a) := p in f a Q
}.

(* ================================================================= *)
(** * Facts and laws (merged from WPArrFacts.v)                          *)
(* ================================================================= *)

(** * Arrow laws for [WPArr].

    The arrow laws reduce to equalities of continuations.  Functional
    extensionality handles functions on products and sums; [app_ext]
    additionally uses equality of the stored arrows. *)

From Coq Require Import FunctionalExtensionality.

#[global]
Instance ArrowLaws_WPArr : @ArrowLaws WPArr Arrow_WPArr ArrowEq_WPArr.
Proof.
  constructor; intros.
  - (* comp_id_l *) reflexivity.
  - (* comp_id_r *) reflexivity.
  - (* comp_assoc *) reflexivity.
  - (* pure_comp *) reflexivity.
  - (* first_pure *)
    apply functional_extensionality; intros [a c].
    apply functional_extensionality; intros Q. reflexivity.
  - (* first_comp *)
    apply functional_extensionality; intros [a c].
    apply functional_extensionality; intros Q. reflexivity.
  - (* first_fst *)
    apply functional_extensionality; intros [a c].
    apply functional_extensionality; intros Q. reflexivity.
  - (* first_assoc *)
    apply functional_extensionality; intros [[a c] d].
    apply functional_extensionality; intros Q. reflexivity.
  - (* comp_proper *)
    intros f1 f2 Hf g1 g2 Hg.
    cbv [arrow_eq ArrowEq_WPArr] in *. subst. reflexivity.
  - (* first_proper *)
    intros f1 f2 Hf.
    cbv [arrow_eq ArrowEq_WPArr] in *. subst. reflexivity.
  - (* first_natural *)
    apply functional_extensionality; intros [a c]. reflexivity.
Qed.

#[global]
Instance ArrowChoiceLaws_WPArr : ArrowChoiceLaws WPArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    apply functional_extensionality; intros [a|c];
    apply functional_extensionality; intros Q; reflexivity.
  - (* left_comp *)
    apply functional_extensionality; intros [a|c];
    apply functional_extensionality; intros Q; reflexivity.
  - (* left_inl *)
    apply functional_extensionality; intros a;
    apply functional_extensionality; intros Q; reflexivity.
  - (* left_assoc *)
    apply functional_extensionality; intros [[a|c]|d];
    apply functional_extensionality; intros Q; reflexivity.
  - (* left_inr *)
    apply functional_extensionality; intros c;
    apply functional_extensionality; intros Q; reflexivity.
  - (* left_natural *)
    apply functional_extensionality; intros [a|c];
    apply functional_extensionality; intros Q; reflexivity.
  - (* first_left_dist *)
    apply functional_extensionality; intros [[a|c] d];
    apply functional_extensionality; intros Q; reflexivity.
  - (* left_proper *)
    intros f1 f2 Hf.
    cbv [arrow_eq ArrowEq_WPArr] in *. subst. reflexivity.
Qed.

#[global]
Instance ArrowApplyLaws_WPArr
  : @ArrowApplyLaws WPArr Arrow_WPArr ArrowApply_WPArr ArrowEq_WPArr.
Proof.
  constructor; [intros | intros | intros | intros | intros X A B u v H].
  - (* app_law *) reflexivity.
  - (* app_unit *)
    apply functional_extensionality; intros [a b]. reflexivity.
  - (* app_precompose *)
    apply functional_extensionality; intros [f a]. reflexivity.
  - (* app_postcompose *)
    apply functional_extensionality; intros [f a]. reflexivity.
  - (* app_ext *)
    apply functional_extensionality; intros x. cbn.
    specialize (H x).
    cbv [arrow_eq ArrowEq_WPArr] in H.
    destruct (u x) as [f a], (v x) as [g a'].
    cbn in H. destruct H as [Hfg Ha].
    change (f = g) in Hfg. change (a = a') in Ha. subst g a'.
    reflexivity.
Qed.
