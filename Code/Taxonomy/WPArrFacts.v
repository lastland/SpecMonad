(** * Arrow laws for [WPArr].

    All of [ArrowLaws], [ArrowChoiceLaws], and [ArrowApplyLaws] hold
    definitionally up to Coq's eta conversion — the proofs are all
    [reflexivity] modulo destructuring of product/sum values. *)

From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness Require Import Taxonomy.WP Taxonomy.WPFacts Taxonomy.WPArr.

#[global]
Instance ArrowLaws_WPArr : ArrowLaws WPArr.
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
Instance ArrowApplyLaws_WPArr : ArrowApplyLaws WPArr.
Proof.
  constructor; intros.
  (* app_law *) reflexivity.
Qed.
