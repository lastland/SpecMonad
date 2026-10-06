(** * Recovered relation contracts and shared complete laws for ASLP. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT ArrowMonad RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure ASLPArrowCore.

Lemma aslpRel_pure {X Y} (h : X -> Y) :
  Rel_eq (aslpRel (pure_ASLP h)) (arr_pure h).
Proof. apply aslpRel_of. intros P y. reflexivity. Qed.
Lemma aslpRel_comp {X Y Z} (w : ASLPArr X Y) (v : ASLPArr Y Z) :
  Rel_eq (aslpRel (comp_ASLP w v)) (arr_comp (aslpRel w) (aslpRel v)).
Proof.
  apply aslpRel_of. intros P z. unfold comp_ASLP, getASLP. cbn [proj1_sig].
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_comp (aslpRel w) (aslpRel v)), (dslpOf_comp (aslpRel w) (aslpRel v)). reflexivity.
Qed.
Lemma aslpRel_first {X Y C} (w : ASLPArr X Y) :
  Rel_eq (aslpRel (@first_ASLP X Y C w)) (arr_first (aslpRel w)).
Proof.
  apply aslpRel_of. intros P q. unfold first_ASLP, getASLP. cbn [proj1_sig].
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_first (aslpRel w)), (dslpOf_first (aslpRel w)). reflexivity.
Qed.
Lemma aslpRel_left {X Y C} (w : ASLPArr X Y) :
  Rel_eq (aslpRel (@left_ASLP X Y C w)) (arr_left (aslpRel w)).
Proof.
  apply aslpRel_of. intros P [b|c]; unfold left_ASLP, getASLP; cbn [proj1_sig]; unfold aslpOf.
  - unfold aspPartA, dslpPartA.
    rewrite (aspOf_left_inl (aslpRel w)), (dslpOf_left_inl (aslpRel w)). reflexivity.
  - rewrite (aspOf_left_inr (aslpRel w)), (dslpOf_left_inr (aslpRel w)). tauto.
Qed.
Lemma aslpRel_app {A B} : Rel_eq (aslpRel (@app_ASLP A B)) appRelA.
Proof. apply aslpRel_of. intros P b. reflexivity. Qed.
Lemma aslpRel_second {X Y C} (w : ASLPArr X Y) :
  Rel_eq (aslpRel (@arr_second ASLPArr Arrow_ASLPArr X Y C w))
    (@arr_second Rel Arrow_Rel X Y C (aslpRel w)).
Proof.
  unfold arr_second. cbn [arr_comp arr_pure arr_first Arrow_ASLPArr].
  repeat first [setoid_rewrite aslpRel_comp | setoid_rewrite aslpRel_pure | setoid_rewrite aslpRel_first].
  reflexivity.
Qed.
Lemma aslpRel_left2 {A B C D} (f : ASLPArr A B) :
  Rel_eq (aslpRel (@left_ASLP _ _ D (@left_ASLP A B C f))) (arr_left (arr_left (aslpRel f))).
Proof. etransitivity; [apply aslpRel_left | apply Rel_left_cong; apply aslpRel_left]. Qed.
Lemma aslpRel_first_left {A B C D} (f : ASLPArr A B) :
  Rel_eq (aslpRel (@first_ASLP _ _ D (@left_ASLP A B C f))) (arr_first (arr_left (aslpRel f))).
Proof. etransitivity; [apply aslpRel_first | apply Rel_first_cong; apply aslpRel_left]. Qed.
Lemma aslpRel_left_first {A B C D} (f : ASLPArr A B) :
  Rel_eq (aslpRel (@left_ASLP _ _ (C * D)%type (@first_ASLP A B D f))) (arr_left (arr_first (aslpRel f))).
Proof. etransitivity; [apply aslpRel_left | apply Rel_left_cong; apply aslpRel_first]. Qed.

#[global] Instance RelArrow_ASLPArr : RelArrow ASLPArr := {|
  rel_reading := @aslpRel; rel_pure := @aslpRel_pure; rel_comp := @aslpRel_comp;
  rel_first := fun A B C f a c b d => aslpRel_first f (a, c) (b, d)
|}.
#[global] Instance RelArrowChoice_ASLPArr : RelArrowChoice ASLPArr := {|rel_left := @aslpRel_left|}.
#[global] Instance RelArrowApply_ASLPArr : RelArrowApply ASLPArr := {|
  rel_app := fun A B f a b => aslpRel_app (f, a) b
|}.
#[global] Instance RelArrowEq_ASLPArr : RelArrowEq ASLPArr := {|
  rel_arrow_eq := fun A B f g => conj (aslpRel_faithful_conv f g) (aslpRel_faithful f g)
|}.
#[global] Instance ArrowLaws_ASLPArr : ArrowLaws ASLPArr :=
  @rel_arrow_laws ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr RelArrow_ASLPArr RelArrowEq_ASLPArr.
#[global] Instance ArrowChoiceLaws_ASLPArr : ArrowChoiceLaws ASLPArr :=
  @rel_arrow_choice_laws ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr RelArrow_ASLPArr
    RelArrowEq_ASLPArr ArrowChoice_ASLPArr RelArrowChoice_ASLPArr.
#[global] Instance ArrowApplyLaws_ASLPArr : ArrowApplyLaws ASLPArr :=
  @rel_arrow_apply_laws ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr RelArrow_ASLPArr
    RelArrowEq_ASLPArr ArrowApply_ASLPArr RelArrowApply_ASLPArr.
