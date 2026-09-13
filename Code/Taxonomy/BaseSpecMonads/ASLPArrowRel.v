(** * [aslpRel] is a faithful arrow morphism, and the laws that follow

    The dual of [DSPArrowRel.v]: every operation of [ASLPArrowCore.v] denotes
    the corresponding [PredArr] operation on the recovered relation, so
    [ArrowLaws] and [ArrowChoiceLaws] are pure transport along [aslpRel].

    [ArrowApplyLaws] is again the exception, proved directly, because
    [arr_app]'s type mentions the arrow itself. *)

From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Classes Require Import ArrowMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASLPArrowCore.

Lemma aslpRel_pure {X Y} (h : X -> Y) :
  Rel_eq (aslpRel (pure_ASLP h)) (arr_pure h).
Proof. apply aslpRel_of. intros P y. reflexivity. Qed.

Lemma aslpRel_comp {X Y Z} (w : ASLPArr X Y) (v : ASLPArr Y Z) :
  Rel_eq (aslpRel (comp_ASLP w v)) (arr_comp (aslpRel w) (aslpRel v)).
Proof.
  apply aslpRel_of. intros P z. unfold comp_ASLP, getASLP. cbn [proj1_sig].
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_comp (aslpRel w) (aslpRel v)), (dslpOf_comp (aslpRel w) (aslpRel v)).
  reflexivity.
Qed.

Lemma aslpRel_first {X Y C} (w : ASLPArr X Y) :
  Rel_eq (aslpRel (@first_ASLP X Y C w)) (arr_first (aslpRel w)).
Proof.
  apply aslpRel_of. intros P q. unfold first_ASLP, getASLP. cbn [proj1_sig].
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_first (aslpRel w)), (dslpOf_first (aslpRel w)).
  reflexivity.
Qed.
Lemma aslpRel_left {X Y C} (w : ASLPArr X Y) :
  Rel_eq (aslpRel (@left_ASLP X Y C w)) (arr_left (aslpRel w)).
Proof.
  apply aslpRel_of. intros P [b|c]; unfold left_ASLP, getASLP; cbn [proj1_sig];
    unfold aslpOf.
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
  unfold arr_second.
  cbn [arr_comp arr_pure arr_first Arrow_ASLPArr].
  repeat first [setoid_rewrite aslpRel_comp | setoid_rewrite aslpRel_pure
    | setoid_rewrite aslpRel_first]. reflexivity.
Qed.


#[local] Ltac to_rel_aslp :=
  apply aslpRel_faithful;
  unfold arr_id; cbn [arr_comp arr_pure arr_first Arrow_ASLPArr];
  rewrite ?aslpRel_comp, ?aslpRel_pure, ?aslpRel_first.

#[global] Instance ArrowLaws_ASLPArr : ArrowLaws ASLPArr.
Proof.
  constructor.
  - intros A B f. to_rel_aslp.
    apply (@comp_id_l Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B f. to_rel_aslp.
    apply (@comp_id_r Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C D f g h. to_rel_aslp.
    apply (@comp_assoc Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C f g. to_rel_aslp.
    apply (@pure_comp Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C f. to_rel_aslp.
    etransitivity; [ apply Rel_first_cong; apply aslpRel_pure |].
    apply (@first_pure Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C D f g. to_rel_aslp.
    etransitivity; [ apply Rel_first_cong; apply aslpRel_comp |].
    apply (@first_comp Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C f. to_rel_aslp.
    apply (@first_fst Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C D f. to_rel_aslp.
    apply (@first_assoc Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros X Y Z w w' Hw v v' Hv. to_rel_aslp.
    apply Rel_comp_cong;
      [ exact (aslpRel_faithful_conv _ _ Hw) | exact (aslpRel_faithful_conv _ _ Hv) ].
  - intros X Y Z w w' Hw. to_rel_aslp.
    apply Rel_first_cong. exact (aslpRel_faithful_conv _ _ Hw).
  - intros A B C D f g. to_rel_aslp.
    apply (@first_natural Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
Qed.


#[local] Ltac to_rel_aslp_a :=
  apply aslpRel_faithful;
  unfold arr_id; cbn [arr_comp arr_pure arr_first arr_app
                      Arrow_ASLPArr ArrowApply_ASLPArr];
  rewrite ?aslpRel_comp, ?aslpRel_pure, ?aslpRel_first, ?aslpRel_app.

#[global] Instance ArrowApplyLaws_ASLPArr : ArrowApplyLaws ASLPArr.
Proof.
  constructor.
  - intros A B f. to_rel_aslp_a. intros a b. unfold appRelA. cbn. split.
    + intros [p [Heq Hp]]. subst p. exact Hp.
    + intro Hf. exists (f, a). split; [ reflexivity | exact Hf ].
  - intros A B. to_rel_aslp_a.
    etransitivity; [ apply Rel_comp_cong; [ apply Rel_first_cong; apply aslpRel_pure | reflexivity ] |].
    intros [a b] q. unfold appRelA. cbn. split.
    + intros [[w b'] [[Hw Hb] Hd]]. cbn in *. subst w. subst b'.
      apply aslpRel_pure in Hd. cbn in Hd. exact Hd.
    + intro Hq. exists (pure_ASLP (fun y : B => (a, y)), b).
      split; [ split; reflexivity |]. cbn. apply aslpRel_pure. exact Hq.
  - (* app_precompose *)
    intros A B C g. to_rel_aslp_a. setoid_rewrite aslpRel_second.
    etransitivity; [apply Rel_comp_cong; [apply Rel_first_cong; apply aslpRel_pure | reflexivity]|].
    intros [f a] c. unfold appRelA, arr_second, swap. cbn. split.
    + intros [[w a'] [[Hw Ha] Hd]]. cbn in *. subst w a'.
      apply aslpRel_comp in Hd. destruct Hd as [b [Hg Hf]].
      exists (f, b). split; [|exact Hf].
      exists (a, f). split; [reflexivity|]. exists (b, f). cbn. auto.
    + intros [[f0 b] [[p [Hp [q [Hg Hq]]]] Hf]].
      destruct p as [a' f'], q as [b' f'']. cbn in *.
      injection Hp as Ha Hf'. subst a' f'.
      destruct Hg as [Hg Hff]. subst f''.
      injection Hq as Hf0 Hb. subst f0 b'.
      exists (comp_ASLP g f, a). cbn. split; [split; reflexivity |].
      apply aslpRel_comp. exists b. auto.
  - intros A B C h. to_rel_aslp_a.
    etransitivity; [ apply Rel_comp_cong; [ apply Rel_first_cong; apply aslpRel_pure | reflexivity ] |].
    intros [f a] c. unfold appRelA. cbn. split.
    + intros [[w a'] [[Hw Ha] Hd]]. cbn in *. subst w. subst a'.
      apply aslpRel_comp in Hd. exact Hd.
    + intros [b [Hab Hbc]]. exists (comp_ASLP f h, a).
      split; [ split; reflexivity |]. cbn.
      apply aslpRel_comp. exists b. split; assumption.
  - intros X A B u v H. to_rel_aslp_a. intros x b. unfold appRelA. cbn.
    specialize (H x). destruct (u x) as [fu au], (v x) as [fv av].
    cbn in H. destruct H as [Hfg Ha]. subst av. split.
    + intros [p [Heq Hp]]. subst p. cbn in Hp.
      exists (fv, au). split; [reflexivity|cbn].
      exact (proj1 (aslpRel_faithful_conv _ _ Hfg au b) Hp).
    + intros [p [Heq Hp]]. subst p. cbn in Hp.
      exists (fu, au). split; [reflexivity|cbn].
      exact (proj2 (aslpRel_faithful_conv _ _ Hfg au b) Hp).
Qed.

(* ----------------------------------------------------------------- *)
(** *** [ArrowChoiceLaws]                                             *)
(* ----------------------------------------------------------------- *)

(** The nested cases, as standalone lemmas.  Stating them separately is what
    makes [left_assoc] and [first_left_dist] go through: every step below is
    then an application at the HEAD of a goal, so nothing is left for
    unification to guess. *)
Lemma aslpRel_left2 {A B C D} (f : ASLPArr A B) :
  Rel_eq (aslpRel (@left_ASLP _ _ D (@left_ASLP A B C f)))
          (arr_left (arr_left (aslpRel f))).
Proof. etransitivity; [ apply aslpRel_left | apply Rel_left_cong; apply aslpRel_left ]. Qed.

Lemma aslpRel_first_left {A B C D} (f : ASLPArr A B) :
  Rel_eq (aslpRel (@first_ASLP _ _ D (@left_ASLP A B C f)))
          (arr_first (arr_left (aslpRel f))).
Proof. etransitivity; [ apply aslpRel_first | apply Rel_first_cong; apply aslpRel_left ]. Qed.

Lemma aslpRel_left_first {A B C D} (f : ASLPArr A B) :
  Rel_eq (aslpRel (@left_ASLP _ _ (C * D)%type (@first_ASLP A B D f)))
          (arr_left (arr_first (aslpRel f))).
Proof. etransitivity; [ apply aslpRel_left | apply Rel_left_cong; apply aslpRel_first ]. Qed.

#[local] Ltac faith_aslp :=
  apply aslpRel_faithful;
  unfold arr_id; cbn [arr_comp arr_pure arr_first arr_left
                      Arrow_ASLPArr ArrowChoice_ASLPArr].

#[local] Ltac to_rel_aslp_c :=
  faith_aslp; rewrite ?aslpRel_comp, ?aslpRel_pure, ?aslpRel_first, ?aslpRel_left.

#[global] Instance ArrowChoiceLaws_ASLPArr : ArrowChoiceLaws ASLPArr.
Proof.
  constructor.
  - intros A B C f. to_rel_aslp_c.
    etransitivity; [ apply Rel_left_cong; apply aslpRel_pure |].
    apply (@left_pure Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f g. to_rel_aslp_c.
    etransitivity; [ apply Rel_left_cong; apply aslpRel_comp |].
    apply (@left_comp Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C f. to_rel_aslp_c.
    apply (@left_inl Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f. faith_aslp.
    etransitivity; [ apply aslpRel_comp |].
    etransitivity; [ apply Rel_comp_cong; [ apply aslpRel_left2 | apply aslpRel_pure ] |].
    etransitivity;
      [ apply (@left_assoc Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
                 ArrowChoiceLaws_Rel) |].
    symmetry.
    etransitivity; [ apply aslpRel_comp |].
    apply Rel_comp_cong; [ apply aslpRel_pure | apply aslpRel_left ].
  - intros A B C f. to_rel_aslp_c.
    apply (@left_inr Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f g. to_rel_aslp_c.
    apply (@left_natural Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f. faith_aslp.
    etransitivity; [ apply aslpRel_comp |].
    etransitivity;
      [ apply Rel_comp_cong; [ apply aslpRel_first_left | apply aslpRel_pure ] |].
    etransitivity;
      [ apply (@first_left_dist Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
                 ArrowChoiceLaws_Rel) |].
    symmetry.
    etransitivity; [ apply aslpRel_comp |].
    apply Rel_comp_cong; [ apply aslpRel_pure | apply aslpRel_left_first ].
  - intros A B C w w' Hw. to_rel_aslp_c.
    apply Rel_left_cong. exact (aslpRel_faithful_conv _ _ Hw).
Qed.
