(** * Recovered relation contracts and shared complete laws for DSP. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT ArrowMonad RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure DSPArrowCore.

Lemma dspRel_pure {X Y} (h : X -> Y) :
  Rel_eq (dspRel (pure_DSP h)) (arr_pure h).
Proof. apply dspRel_of. intros P y. reflexivity. Qed.
Lemma dspRel_comp {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z) :
  Rel_eq (dspRel (comp_DSP w v)) (arr_comp (dspRel w) (dspRel v)).
Proof.
  apply dspRel_of. intros P z. unfold comp_DSP, getDSP. cbn [proj1_sig].
  unfold aspPart, dslpPart, dspOf.
  rewrite (aspOf_comp (dspRel w) (dspRel v)), (dslpOf_comp (dspRel w) (dspRel v)).
  reflexivity.
Qed.
Lemma dspRel_first {X Y C} (w : DSPArr X Y) :
  Rel_eq (dspRel (@first_DSP X Y C w)) (arr_first (dspRel w)).
Proof.
  apply dspRel_of. intros P q. unfold first_DSP, getDSP. cbn [proj1_sig].
  unfold aspPart, dslpPart, dspOf.
  rewrite (aspOf_first (dspRel w)), (dslpOf_first (dspRel w)). reflexivity.
Qed.
Lemma dspRel_left {X Y C} (w : DSPArr X Y) :
  Rel_eq (dspRel (@left_DSP X Y C w)) (arr_left (dspRel w)).
Proof.
  apply dspRel_of. intros P [b|c]; unfold left_DSP, getDSP; cbn [proj1_sig]; unfold dspOf.
  - unfold aspPart, dslpPart.
    rewrite (aspOf_left_inl (dspRel w)), (dslpOf_left_inl (dspRel w)). reflexivity.
  - rewrite (aspOf_left_inr (dspRel w)), (dslpOf_left_inr (dspRel w)). tauto.
Qed.
Lemma dspRel_app {A B} : Rel_eq (dspRel (@app_DSP A B)) appRel.
Proof. apply dspRel_of. intros P b. reflexivity. Qed.
Lemma dspRel_second {X Y C} (w : DSPArr X Y) :
  Rel_eq (dspRel (@arr_second DSPArr Arrow_DSPArr X Y C w))
    (@arr_second Rel Arrow_Rel X Y C (dspRel w)).
Proof.
  unfold arr_second. cbn [arr_comp arr_pure arr_first Arrow_DSPArr].
  repeat first [setoid_rewrite dspRel_comp | setoid_rewrite dspRel_pure | setoid_rewrite dspRel_first].
  reflexivity.
Qed.
Lemma dspRel_pure_sym {X Y} (h : X -> Y) : Rel_eq (arr_pure h) (dspRel (pure_DSP h)).
Proof. intros x y. symmetry. apply dspRel_pure. Qed.
Lemma dspRel_comp_sym {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z) :
  Rel_eq (arr_comp (dspRel w) (dspRel v)) (dspRel (comp_DSP w v)).
Proof. intros x z. symmetry. apply dspRel_comp. Qed.
Lemma dspRel_first_sym {X Y C} (w : DSPArr X Y) :
  Rel_eq (arr_first (dspRel w)) (dspRel (@first_DSP X Y C w)).
Proof. intros p q. symmetry. apply dspRel_first. Qed.
Lemma dspRel_left2 {A B C D} (f : DSPArr A B) :
  Rel_eq (dspRel (@left_DSP _ _ D (@left_DSP A B C f))) (arr_left (arr_left (dspRel f))).
Proof. etransitivity; [apply dspRel_left | apply Rel_left_cong; apply dspRel_left]. Qed.
Lemma dspRel_first_left {A B C D} (f : DSPArr A B) :
  Rel_eq (dspRel (@first_DSP _ _ D (@left_DSP A B C f))) (arr_first (arr_left (dspRel f))).
Proof. etransitivity; [apply dspRel_first | apply Rel_first_cong; apply dspRel_left]. Qed.
Lemma dspRel_left_first {A B C D} (f : DSPArr A B) :
  Rel_eq (dspRel (@left_DSP _ _ (C * D)%type (@first_DSP A B D f))) (arr_left (arr_first (dspRel f))).
Proof. etransitivity; [apply dspRel_left | apply Rel_left_cong; apply dspRel_first]. Qed.

#[global] Instance RelArrow_DSPArr : RelArrow DSPArr := {|
  rel_reading := @dspRel; rel_pure := @dspRel_pure; rel_comp := @dspRel_comp;
  rel_first := fun A B C f a c b d => dspRel_first f (a, c) (b, d)
|}.
#[global] Instance RelArrowChoice_DSPArr : RelArrowChoice DSPArr := {|rel_left := @dspRel_left|}.
#[global] Instance RelArrowApply_DSPArr : RelArrowApply DSPArr := {|
  rel_app := fun A B f a b => dspRel_app (f, a) b
|}.
#[global] Instance RelArrowEq_DSPArr : RelArrowEq DSPArr := {|
  rel_arrow_eq := fun A B f g => conj (dspRel_faithful_conv f g) (dspRel_faithful f g)
|}.
#[global] Instance ArrowLaws_DSPArr : ArrowLaws DSPArr :=
  @rel_arrow_laws DSPArr Arrow_DSPArr ArrowEq_DSPArr RelArrow_DSPArr RelArrowEq_DSPArr.
#[global] Instance ArrowChoiceLaws_DSPArr : ArrowChoiceLaws DSPArr :=
  @rel_arrow_choice_laws DSPArr Arrow_DSPArr ArrowEq_DSPArr RelArrow_DSPArr
    RelArrowEq_DSPArr ArrowChoice_DSPArr RelArrowChoice_DSPArr.
#[global] Instance ArrowApplyLaws_DSPArr : ArrowApplyLaws DSPArr :=
  @rel_arrow_apply_laws DSPArr Arrow_DSPArr ArrowEq_DSPArr RelArrow_DSPArr
    RelArrowEq_DSPArr ArrowApply_DSPArr RelArrowApply_DSPArr.
