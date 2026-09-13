(** * [dspRel] is a faithful arrow morphism, and the laws that follow

    Every operation of [DSPArrowCore.v] denotes the corresponding [PredArr]
    operation on the recovered relation, and an element is determined by that
    relation.  So each arrow law is [PredArr]'s, read through [dspRel]:
    [ArrowLaws] and [ArrowChoiceLaws] are pure transport.

    [ArrowApplyLaws] is the exception and is proved directly: [arr_app]'s type
    mentions the arrow itself, so [PredArr]'s [arr_app] lives at a different
    domain and its laws are not instances of these.  They are short anyway,
    because [appRel] is defined BY the recovered relation -- applying an arrow
    is, relationally, looking its relation up. *)

From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Classes Require Import ArrowMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSPArrowCore.

(* ----------------------------------------------------------------- *)
(** *** [dspRel] is a faithful arrow morphism                         *)
(* ----------------------------------------------------------------- *)

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
  rewrite (aspOf_first (dspRel w)), (dslpOf_first (dspRel w)).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
Lemma dspRel_left {X Y C} (w : DSPArr X Y) :
  Rel_eq (dspRel (@left_DSP X Y C w)) (arr_left (dspRel w)).
Proof.
  apply dspRel_of. intros P [b|c]; unfold left_DSP, getDSP; cbn [proj1_sig];
    unfold dspOf.
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
  unfold arr_second.
  cbn [arr_comp arr_pure arr_first Arrow_DSPArr].
  repeat first [setoid_rewrite dspRel_comp | setoid_rewrite dspRel_pure
    | setoid_rewrite dspRel_first]. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The arrow laws, transported                                   *)
(* ----------------------------------------------------------------- *)

(** Every law is [PredArr]'s, read through [dspRel]: push the morphism
    through both sides and apply the corresponding [ArrowLaws_Pred] field.
    Nothing here is specific to DSP. *)

(** The same three, oriented for use on the right of a goal. *)
Lemma dspRel_pure_sym {X Y} (h : X -> Y) :
  Rel_eq (arr_pure h) (dspRel (pure_DSP h)).
Proof. intros x y. symmetry. apply dspRel_pure. Qed.

Lemma dspRel_comp_sym {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z) :
  Rel_eq (arr_comp (dspRel w) (dspRel v)) (dspRel (comp_DSP w v)).
Proof. intros x z. symmetry. apply dspRel_comp. Qed.

Lemma dspRel_first_sym {X Y C} (w : DSPArr X Y) :
  Rel_eq (arr_first (dspRel w)) (dspRel (@first_DSP X Y C w)).
Proof. intros p q. symmetry. apply dspRel_first. Qed.

(** Reduce a law about [DSPArr] to the same law about the relations it
    denotes.  [dspRel_comp] / [dspRel_pure] / [dspRel_first] fire at the head;
    occurrences nested inside [arr_comp] or [arr_first] are reached with
    [Pred_comp_cong] / [Pred_first_cong]. *)
#[local] Ltac to_rel :=
  apply dspRel_faithful;
  unfold arr_id; cbn [arr_comp arr_pure arr_first Arrow_DSPArr];
  rewrite ?dspRel_comp, ?dspRel_pure, ?dspRel_first.

#[global] Instance ArrowLaws_DSPArr : ArrowLaws DSPArr.
Proof.
  constructor.
  - intros A B f. to_rel.
    apply (@comp_id_l Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B f. to_rel.
    apply (@comp_id_r Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C D f g h. to_rel.
    apply (@comp_assoc Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C f g. to_rel.
    apply (@pure_comp Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C f. to_rel.
    etransitivity; [ apply Rel_first_cong; apply dspRel_pure |].
    apply (@first_pure Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C D f g. to_rel.
    etransitivity; [ apply Rel_first_cong; apply dspRel_comp |].
    apply (@first_comp Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C f. to_rel.
    apply (@first_fst Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros A B C D f. to_rel.
    apply (@first_assoc Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  - intros X Y Z w w' Hw v v' Hv. to_rel.
    apply Rel_comp_cong;
      [ exact (dspRel_faithful_conv _ _ Hw) | exact (dspRel_faithful_conv _ _ Hv) ].
  - intros X Y Z w w' Hw. to_rel.
    apply Rel_first_cong. exact (dspRel_faithful_conv _ _ Hw).
  - intros A B C D f g. to_rel.
    apply (@first_natural Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
Qed.


(** *** [ArrowApplyLaws], proved directly                             *)
(* ----------------------------------------------------------------- *)

(** These do NOT transport from [PredArr]: [arr_app]'s type mentions the
    arrow itself, so [PredArr]'s [arr_app] lives at a different domain
    ([PredArr A B * A] rather than [DSPArr A B * A]) and its laws are not
    instances of these.  Each is proved from [appRel]'s definition instead.

    What makes them go through is that [appRel] is DEFINED by the recovered
    relation -- [appRel (w, a) b := dspRel w a b] -- so applying an arrow is,
    relationally, just looking that arrow's relation up.  Each law then says
    something the composite relation makes obvious. *)

#[local] Ltac to_rel_a :=
  apply dspRel_faithful;
  unfold arr_id; cbn [arr_comp arr_pure arr_first arr_app
                      Arrow_DSPArr ArrowApply_DSPArr];
  rewrite ?dspRel_comp, ?dspRel_pure, ?dspRel_first, ?dspRel_app.

#[global] Instance ArrowApplyLaws_DSPArr : ArrowApplyLaws DSPArr.
Proof.
  constructor.
  - (* app_law : feeding [f] to [arr_app] is [f] *)
    intros A B f. to_rel_a. intros a b. unfold appRel. cbn. split.
    + intros [p [Heq Hp]]. subst p. exact Hp.
    + intro Hf. exists (f, a). split; [ reflexivity | exact Hf ].
  - (* app_pair : pairing then applying is the identity *)
    intros A B. to_rel_a.
    etransitivity; [ apply Rel_comp_cong; [ apply Rel_first_cong; apply dspRel_pure | reflexivity ] |].
    intros [a b] q. unfold appRel. cbn. split.
    + intros [[w b'] [[Hw Hb] Hd]]. cbn in *. subst w. subst b'.
      apply dspRel_pure in Hd. cbn in Hd. exact Hd.
    + intro Hq. exists (pure_DSP (fun y : B => (a, y)), b).
      split; [ split; reflexivity |]. cbn. apply dspRel_pure. exact Hq.
  - (* app_precompose *)
    intros A B C g. to_rel_a. setoid_rewrite dspRel_second.
    etransitivity; [apply Rel_comp_cong; [apply Rel_first_cong; apply dspRel_pure | reflexivity]|].
    intros [f a] c. unfold appRel, arr_second, swap. cbn. split.
    + intros [[w a'] [[Hw Ha] Hd]]. cbn in *. subst w a'.
      apply dspRel_comp in Hd. destruct Hd as [b [Hg Hf]].
      exists (f, b). split; [|exact Hf].
      exists (a, f). split; [reflexivity|]. exists (b, f). cbn. auto.
    + intros [[f0 b] [[p [Hp [q [Hg Hq]]]] Hf]].
      destruct p as [a' f'], q as [b' f'']. cbn in *.
      injection Hp as Ha Hf'. subst a' f'.
      destruct Hg as [Hg Hff]. subst f''.
      injection Hq as Hf0 Hb. subst f0 b'.
      exists (comp_DSP g f, a). cbn. split; [split; reflexivity |].
      apply dspRel_comp. exists b. auto.
  - (* app_postcompose : post-composing before applying *)
    intros A B C h. to_rel_a.
    etransitivity; [ apply Rel_comp_cong; [ apply Rel_first_cong; apply dspRel_pure | reflexivity ] |].
    intros [f a] c. unfold appRel. cbn. split.
    + intros [[w a'] [[Hw Ha] Hd]]. cbn in *. subst w. subst a'.
      apply dspRel_comp in Hd. exact Hd.
    + intros [b [Hab Hbc]]. exists (comp_DSP f h, a).
      split; [ split; reflexivity |]. cbn.
      apply dspRel_comp. exists b. split; assumption.
  - (* app_ext : [arr_app] sees only the arrow's extension *)
    intros X A B u v H. to_rel_a. intros x b. unfold appRel. cbn.
    specialize (H x). destruct (u x) as [fu au], (v x) as [fv av].
    cbn in H. destruct H as [Hfg Ha]. subst av. split.
    + intros [p [Heq Hp]]. subst p. cbn in Hp.
      exists (fv, au). split; [reflexivity|cbn].
      exact (proj1 (dspRel_faithful_conv _ _ Hfg au b) Hp).
    + intros [p [Heq Hp]]. subst p. cbn in Hp.
      exists (fu, au). split; [reflexivity|cbn].
      exact (proj2 (dspRel_faithful_conv _ _ Hfg au b) Hp).
Qed.

(* ----------------------------------------------------------------- *)
(** *** [ArrowChoiceLaws]                                             *)
(* ----------------------------------------------------------------- *)

(** The nested cases, as standalone lemmas.  Stating them separately is what
    makes [left_assoc] and [first_left_dist] go through: every step below is
    then an application at the HEAD of a goal, so nothing is left for
    unification to guess. *)

Lemma dspRel_left2 {A B C D} (f : DSPArr A B) :
  Rel_eq (dspRel (@left_DSP _ _ D (@left_DSP A B C f)))
          (arr_left (arr_left (dspRel f))).
Proof. etransitivity; [ apply dspRel_left | apply Rel_left_cong; apply dspRel_left ]. Qed.

Lemma dspRel_first_left {A B C D} (f : DSPArr A B) :
  Rel_eq (dspRel (@first_DSP _ _ D (@left_DSP A B C f)))
          (arr_first (arr_left (dspRel f))).
Proof. etransitivity; [ apply dspRel_first | apply Rel_first_cong; apply dspRel_left ]. Qed.

Lemma dspRel_left_first {A B C D} (f : DSPArr A B) :
  Rel_eq (dspRel (@left_DSP _ _ (C * D)%type (@first_DSP A B D f)))
          (arr_left (arr_first (dspRel f))).
Proof. etransitivity; [ apply dspRel_left | apply Rel_left_cong; apply dspRel_first ]. Qed.

#[local] Ltac faith :=
  apply dspRel_faithful;
  unfold arr_id; cbn [arr_comp arr_pure arr_first arr_left
                      Arrow_DSPArr ArrowChoice_DSPArr].

#[local] Ltac to_rel_c :=
  faith; rewrite ?dspRel_comp, ?dspRel_pure, ?dspRel_first, ?dspRel_left.

#[global] Instance ArrowChoiceLaws_DSPArr : ArrowChoiceLaws DSPArr.
Proof.
  constructor.
  - intros A B C f. to_rel_c.
    etransitivity; [ apply Rel_left_cong; apply dspRel_pure |].
    apply (@left_pure Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f g. to_rel_c.
    etransitivity; [ apply Rel_left_cong; apply dspRel_comp |].
    apply (@left_comp Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C f. to_rel_c.
    apply (@left_inl Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f. faith.
    etransitivity; [ apply dspRel_comp |].
    etransitivity; [ apply Rel_comp_cong; [ apply dspRel_left2 | apply dspRel_pure ] |].
    etransitivity;
      [ apply (@left_assoc Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
                 ArrowChoiceLaws_Rel) |].
    symmetry.
    etransitivity; [ apply dspRel_comp |].
    apply Rel_comp_cong; [ apply dspRel_pure | apply dspRel_left ].
  - intros A B C f. to_rel_c.
    apply (@left_inr Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f g. to_rel_c.
    apply (@left_natural Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
             ArrowChoiceLaws_Rel).
  - intros A B C D f. faith.
    etransitivity; [ apply dspRel_comp |].
    etransitivity;
      [ apply Rel_comp_cong; [ apply dspRel_first_left | apply dspRel_pure ] |].
    etransitivity;
      [ apply (@first_left_dist Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
                 ArrowChoiceLaws_Rel) |].
    symmetry.
    etransitivity; [ apply dspRel_comp |].
    apply Rel_comp_cong; [ apply dspRel_pure | apply dspRel_left_first ].
  - intros A B C w w' Hw. to_rel_c.
    apply Rel_left_cong. exact (dspRel_faithful_conv _ _ Hw).
Qed.
