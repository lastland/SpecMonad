(** * Laws for [RelPrePost].

    This file collects the Yoneda-probe characterization lemmas
    ([yoneda_at_arr_pure], [yoneda_at_arr_comp], etc.) and proves
    [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws], [Eq1Equivalence]
    and [MonadLawsE] for [RelPrePost]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness Require Import Taxonomy.RelPrePost.

(* ================================================================= *)
(** ** Yoneda-probe characterization lemmas                           *)
(* ================================================================= *)

(** [yoneda_at] of an arrow operation reduces to a clean formula. *)

Lemma yoneda_at_arr_pure {A B} (f : A -> B) (a : A) (Q : B -> Prop) :
  yoneda_at (@arr_pure _ Arrow_RelPrePost A B f) a Q <-> Q (f a).
Proof.
  unfold yoneda_at; cbn. split.
  - intros [P [R [HPR [HPa Hiff]]]]. apply Hiff. apply HPR. exact HPa.
  - intros HQ. exists (eq a), (fun a' b => a' = a -> Q b). split; [|split].
    + intros a' Heq. subst a'. intros _. exact HQ.
    + reflexivity.
    + intros b. split; [intros H; apply H; reflexivity | intros HQb _; exact HQb].
Qed.

Lemma yoneda_at_arr_comp {A B C} (r : RelPrePost A B) (s : RelPrePost B C)
  (a : A) (Q : C -> Prop) :
  yoneda_at (@arr_comp _ Arrow_RelPrePost A B C r s) a Q
  <-> yoneda_at r a (fun b => yoneda_at s b Q).
Proof.
  unfold yoneda_at at 1; cbn. split.
  - intros [P [R [HPR [HPa Hiff]]]].
    specialize (HPR a HPa).
    (* HPR : yoneda_at r a (fun b => yoneda_at s b (R a))
       Goal : yoneda_at r a (fun b => yoneda_at s b Q)
       Use Proper of yoneda_at to swap (R a) with Q via Hiff. *)
    enough (Hyo : yoneda_at r a (fun b => yoneda_at s b (R a))
                  <-> yoneda_at r a (fun b => yoneda_at s b Q))
      by (apply Hyo; exact HPR).
    apply yoneda_at_Proper. intros b.
    apply yoneda_at_Proper. exact Hiff.
  - intros Hr.
    exists (eq a), (fun a' c => a' = a -> Q c).
    split; [|split].
    + intros a' Heq. subst a'.
      enough (Hyo : yoneda_at r a (fun b => yoneda_at s b Q)
                    <-> yoneda_at r a (fun b => yoneda_at s b (fun c => a = a -> Q c)))
        by (apply Hyo; exact Hr).
      apply yoneda_at_Proper. intros b.
      apply yoneda_at_Proper. intros c. tauto.
    + reflexivity.
    + intros c. tauto.
Qed.

Lemma yoneda_at_arr_left {A B C} (r : RelPrePost A B)
  (x : A + C) (Q : (B + C) -> Prop) :
  yoneda_at (@arr_left _ _ _ A B C r) x Q
  <-> match x with
      | inl a => yoneda_at r a (fun b => Q (inl b))
      | inr c => Q (inr c)
      end.
Proof.
  unfold yoneda_at at 1; cbn. split.
  - intros [P [R [HPR [HPx Hiff]]]].
    specialize (HPR x HPx).
    destruct x as [a|c].
    + (* inl a *)
      enough (Hyo : yoneda_at r a (fun b => R (inl a) (inl b))
                    <-> yoneda_at r a (fun b => Q (inl b)))
        by (apply Hyo; exact HPR).
      apply yoneda_at_Proper. intros b. apply (Hiff (inl b)).
    + (* inr c *)
      apply (proj1 (Hiff (inr c))). exact HPR.
  - destruct x as [a|c]; intros H.
    + (* inl a *)
      exists (eq (inl a)), (fun x' y => x' = inl a -> Q y).
      split; [|split].
      * intros x' Heq. subst x'. cbn.
        enough (Hyo : yoneda_at r a (fun b => Q (inl b))
                      <-> yoneda_at r a (fun b => inl a = inl a -> Q (inl b)))
          by (apply Hyo; exact H).
        apply yoneda_at_Proper. intros b. tauto.
      * reflexivity.
      * intros y. tauto.
    + (* inr c *)
      exists (eq (inr c)), (fun x' y => x' = inr c -> Q y).
      split; [|split].
      * intros x' Heq. subst x'. cbn. intros _. exact H.
      * reflexivity.
      * intros y. tauto.
Qed.

Lemma yoneda_at_arr_app {A B}
  (x : (RelPrePost A B * A)%type) (Q : B -> Prop) :
  yoneda_at (@arr_app _ _ ArrowApply_RelPrePost A B) x Q
  <-> (let '(r, a) := x in yoneda_at r a Q).
Proof.
  unfold yoneda_at at 1; cbn. split.
  - intros [P [R [HPR [HPx Hiff]]]].
    specialize (HPR x HPx).
    destruct x as [r a]. cbn in HPR.
    enough (Hyo : yoneda_at r a (fun b => R (r, a) b)
                  <-> yoneda_at r a Q)
      by (apply Hyo; exact HPR).
    apply yoneda_at_Proper. intros b. apply Hiff.
  - destruct x as [r a]. intros H.
    exists (eq (r, a)), (fun x' y => x' = (r, a) -> Q y).
    split; [|split].
    + intros x' Heq. subst x'. cbn.
      enough (Hyo : yoneda_at r a Q
                    <-> yoneda_at r a (fun b => (r, a) = (r, a) -> Q b))
        by (apply Hyo; exact H).
      apply yoneda_at_Proper. intros b. tauto.
    + reflexivity.
    + intros y. tauto.
Qed.

Lemma yoneda_at_arr_first {A B C} (r : RelPrePost A B)
  (p : A * C) (Q : B * C -> Prop) :
  yoneda_at (@arr_first _ Arrow_RelPrePost A B C r) p Q
  <-> yoneda_at r (fst p) (fun b => Q (b, snd p)).
Proof.
  unfold yoneda_at at 1; cbn. split.
  - intros [P [R [HPR [HPp Hiff]]]].
    specialize (HPR p HPp).
    enough (Hyo : yoneda_at r (fst p) (fun b => R p (b, snd p))
                  <-> yoneda_at r (fst p) (fun b => Q (b, snd p)))
      by (apply Hyo; exact HPR).
    apply yoneda_at_Proper. intros b. apply (Hiff (b, snd p)).
  - intros Hr.
    exists (eq p), (fun p' bc => p' = p -> Q bc).
    split; [|split].
    + intros p' Heq. subst p'.
      enough (Hyo : yoneda_at r (fst p) (fun b => Q (b, snd p))
                    <-> yoneda_at r (fst p) (fun b => p = p -> Q (b, snd p)))
        by (apply Hyo; exact Hr).
      apply yoneda_at_Proper. intros b. tauto.
    + reflexivity.
    + intros bc. tauto.
Qed.

(** Specialized versions of [yoneda_at_arr_left] that handle [inl] and
    [inr] without a match.  Convenient for [rewrite]. *)
Lemma yoneda_at_arr_left_inl {A B C} (r : RelPrePost A B)
  (a : A) (Q : (B + C) -> Prop) :
  yoneda_at (@arr_left _ _ _ A B C r) (inl a) Q
  <-> yoneda_at r a (fun b => Q (inl b)).
Proof. rewrite yoneda_at_arr_left. reflexivity. Qed.

Lemma yoneda_at_arr_left_inr {A B C} (r : RelPrePost A B)
  (c : C) (Q : (B + C) -> Prop) :
  yoneda_at (@arr_left _ _ _ A B C r) (inr c) Q
  <-> Q (inr c).
Proof. rewrite yoneda_at_arr_left. reflexivity. Qed.

(** Specialized version of [yoneda_at_arr_first] that takes a destructured
    pair, avoiding unreduced [fst]/[snd]. *)
Lemma yoneda_at_arr_first_pair {A B C} (r : RelPrePost A B)
  (a : A) (c : C) (Q : B * C -> Prop) :
  yoneda_at (@arr_first _ Arrow_RelPrePost A B C r) (a, c) Q
  <-> yoneda_at r a (fun b => Q (b, c)).
Proof. rewrite yoneda_at_arr_first. reflexivity. Qed.

(* ================================================================= *)
(** ** Arrow laws                                                     *)
(* ================================================================= *)

#[global]
Instance ArrowLaws_RelPrePost : ArrowLaws RelPrePost.
Proof.
  constructor; intros.
  - (* comp_id_l: arr_comp arr_id f ≡ f *)
    intros a Q. rewrite yoneda_at_arr_comp.
    unfold arr_id. setoid_rewrite yoneda_at_arr_pure.
    reflexivity.
  - (* comp_id_r: arr_comp f arr_id ≡ f *)
    intros a Q. rewrite yoneda_at_arr_comp.
    unfold arr_id.
    apply yoneda_at_Proper. intros b. rewrite yoneda_at_arr_pure.
    reflexivity.
  - (* comp_assoc *)
    intros a Q. rewrite !yoneda_at_arr_comp.
    apply yoneda_at_Proper. intros b. rewrite yoneda_at_arr_comp.
    reflexivity.
  - (* pure_comp *)
    intros a Q. rewrite yoneda_at_arr_comp, !yoneda_at_arr_pure.
    reflexivity.
  - (* first_pure *)
    intros p Q. rewrite yoneda_at_arr_first, !yoneda_at_arr_pure.
    destruct p as [a c]; cbn. reflexivity.
  - (* first_comp *)
    intros p Q.
    rewrite yoneda_at_arr_first.
    rewrite yoneda_at_arr_comp.
    rewrite yoneda_at_arr_comp.
    rewrite yoneda_at_arr_first.
    apply yoneda_at_Proper. intros b.
    rewrite yoneda_at_arr_first.
    destruct p as [a d]; cbn. reflexivity.
  - (* first_fst *)
    intros p Q.
    rewrite yoneda_at_arr_comp.
    rewrite yoneda_at_arr_first.
    rewrite yoneda_at_arr_comp.
    setoid_rewrite yoneda_at_arr_pure.
    destruct p as [a c]; cbn.
    reflexivity.
  - (* first_assoc *)
    intros p Q.
    rewrite yoneda_at_arr_comp.
    rewrite yoneda_at_arr_first.
    rewrite yoneda_at_arr_first.
    rewrite yoneda_at_arr_comp.
    setoid_rewrite yoneda_at_arr_pure.
    setoid_rewrite yoneda_at_arr_first.
    destruct p as [[a c] d]; cbn.
    unfold assoc_prod; cbn.
    reflexivity.
  - (* comp_proper *)
    intros r1 r2 Hr s1 s2 Hs a Q.
    rewrite !yoneda_at_arr_comp.
    rewrite (Hr a). apply yoneda_at_Proper. intros b. apply Hs.
  - (* first_proper *)
    intros r1 r2 Hr p Q.
    rewrite !yoneda_at_arr_first.
    apply Hr.
Qed.

#[global]
Instance ArrowChoiceLaws_RelPrePost : ArrowChoiceLaws RelPrePost.
Proof.
  constructor; intros.
  - (* left_pure *)
    intros x Q. destruct x as [a|c].
    + rewrite yoneda_at_arr_left_inl, !yoneda_at_arr_pure.
      unfold sum_bimap. reflexivity.
    + rewrite yoneda_at_arr_left_inr, yoneda_at_arr_pure.
      unfold sum_bimap. reflexivity.
  - (* left_comp *)
    intros x Q. destruct x as [a|c].
    + rewrite yoneda_at_arr_left_inl, !yoneda_at_arr_comp.
      rewrite yoneda_at_arr_left_inl. cbv beta.
      setoid_rewrite yoneda_at_arr_left_inl.
      reflexivity.
    + rewrite yoneda_at_arr_left_inr, yoneda_at_arr_comp.
      rewrite yoneda_at_arr_left_inr. cbv beta.
      rewrite yoneda_at_arr_left_inr. reflexivity.
  - (* left_inl *)
    intros a Q.
    rewrite !yoneda_at_arr_comp.
    setoid_rewrite yoneda_at_arr_pure.
    rewrite yoneda_at_arr_left_inl.
    reflexivity.
  - (* left_assoc *)
    intros x Q.
    rewrite !yoneda_at_arr_comp.
    setoid_rewrite yoneda_at_arr_pure.
    destruct x as [[a|c]|d].
    + (* inl (inl a) *)
      rewrite yoneda_at_arr_left_inl. cbv beta.
      rewrite yoneda_at_arr_left_inl. cbv beta.
      unfold assoc_sum; cbv iota.
      rewrite yoneda_at_arr_left_inl.
      reflexivity.
    + (* inl (inr c) *)
      rewrite yoneda_at_arr_left_inl. cbv beta.
      rewrite yoneda_at_arr_left_inr. cbv beta.
      unfold assoc_sum; cbv iota.
      rewrite yoneda_at_arr_left_inr.
      reflexivity.
    + (* inr d *)
      rewrite yoneda_at_arr_left_inr. cbv beta.
      unfold assoc_sum; cbv iota.
      rewrite yoneda_at_arr_left_inr.
      reflexivity.
  - (* left_inr *)
    intros c Q.
    rewrite yoneda_at_arr_comp.
    setoid_rewrite yoneda_at_arr_pure.
    cbv beta.
    rewrite yoneda_at_arr_left_inr.
    reflexivity.
  - (* left_natural *)
    intros x Q.
    rewrite !yoneda_at_arr_comp.
    setoid_rewrite yoneda_at_arr_pure.
    destruct x as [a|c].
    + (* inl a *)
      rewrite yoneda_at_arr_left_inl. cbv beta.
      unfold sum_bimap; cbv iota.
      rewrite yoneda_at_arr_left_inl.
      reflexivity.
    + (* inr c *)
      rewrite yoneda_at_arr_left_inr. cbv beta.
      unfold sum_bimap; cbv iota.
      rewrite yoneda_at_arr_left_inr.
      reflexivity.
  - (* first_left_dist *)
    intros p Q.
    destruct p as [x d].
    rewrite !yoneda_at_arr_comp.
    rewrite yoneda_at_arr_first_pair.
    setoid_rewrite yoneda_at_arr_pure.
    destruct x as [a|c].
    + (* inl a *)
      rewrite yoneda_at_arr_left_inl. cbv beta.
      unfold sum_prod_dist; cbv iota.
      rewrite yoneda_at_arr_left_inl.
      rewrite yoneda_at_arr_first_pair.
      reflexivity.
    + (* inr c *)
      rewrite yoneda_at_arr_left_inr. cbv beta.
      unfold sum_prod_dist; cbv iota.
      rewrite yoneda_at_arr_left_inr.
      reflexivity.
  - (* left_proper *)
    intros r1 r2 Hr x Q. destruct x as [a|c].
    + rewrite !yoneda_at_arr_left_inl. apply Hr.
    + rewrite !yoneda_at_arr_left_inr. reflexivity.
Qed.

#[global]
Instance ArrowApplyLaws_RelPrePost : ArrowApplyLaws RelPrePost.
Proof.
  constructor; intros.
  (* app_law: arr_comp (arr_pure (fun a => (f, a))) arr_app ≡ f *)
  intros a Q.
  rewrite yoneda_at_arr_comp, yoneda_at_arr_pure.
  rewrite yoneda_at_arr_app.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Monad laws                                                     *)
(* ================================================================= *)

Section RelPrePostMonadLaws.

  Context {A : Type}.

  #[global]
  Instance Eq1Equivalence_RelPrePost
    : @Eq1Equivalence (RelPrePost A) _ Eq1_RelPrePost.
  Proof.
    intros B; constructor.
    - intros r a Q. reflexivity.
    - intros r1 r2 H a Q. symmetry. apply H.
    - intros r1 r2 r3 H12 H23 a Q. etransitivity; [apply H12 | apply H23].
  Qed.

  Lemma yoneda_at_ret {B} (b : B) (a : A) (Q : B -> Prop) :
    yoneda_at (retRelPrePost b) a Q <-> Q b.
  Proof.
    unfold yoneda_at, retRelPrePost. split.
    - intros [P [R [HPR [HPa Hiff]]]]. apply Hiff. apply HPR. exact HPa.
    - intros HQ. exists (eq a), (fun a' b' => a' = a -> Q b'). split; [|split].
      + intros a' Heq. subst a'. intros _. exact HQ.
      + reflexivity.
      + intros b'. split; [intros H; apply H; reflexivity | intros HQb _; exact HQb].
  Qed.

  Lemma yoneda_at_bind {B C}
    (r : RelPrePost A B) (k : B -> RelPrePost A C) (a : A) (Q : C -> Prop) :
    yoneda_at (bindRelPrePost r k) a Q
    <-> yoneda_at r a (fun b => yoneda_at (k b) a Q).
  Proof.
    unfold yoneda_at at 1, bindRelPrePost. split.
    - intros [P [R [HPR [HPa Hiff]]]].
      specialize (HPR a HPa).
      enough (Hyo : yoneda_at r a (fun b => yoneda_at (k b) a (R a))
                    <-> yoneda_at r a (fun b => yoneda_at (k b) a Q))
        by (apply Hyo; exact HPR).
      apply yoneda_at_Proper. intros b.
      apply yoneda_at_Proper. exact Hiff.
    - intros Hr.
      exists (eq a), (fun a' c => a' = a -> Q c).
      split; [|split].
      + intros a' Heq. subst a'.
        enough (Hyo : yoneda_at r a (fun b => yoneda_at (k b) a Q)
                      <-> yoneda_at r a (fun b => yoneda_at (k b) a (fun c => a = a -> Q c)))
          by (apply Hyo; exact Hr).
        apply yoneda_at_Proper. intros b.
        apply yoneda_at_Proper. intros c. tauto.
      + reflexivity.
      + intros c. tauto.
  Qed.

  #[global]
  Instance MonadLawsE_RelPrePost
    : @MonadLawsE (RelPrePost A) Eq1_RelPrePost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros B C f x.
      intros a Q. cbn. rewrite yoneda_at_bind, yoneda_at_ret. reflexivity.
    - (* bind_ret_r *)
      intros B m. intros a Q. cbn. rewrite yoneda_at_bind.
      setoid_rewrite yoneda_at_ret. reflexivity.
    - (* bind_bind *)
      intros B C D m f g.
      intros a Q. cbn. rewrite !yoneda_at_bind.
      setoid_rewrite yoneda_at_bind. reflexivity.
    - (* Proper_bind *)
      intros B C m1 m2 Hm k1 k2 Hk a Q. cbn.
      rewrite !yoneda_at_bind.
      unfold eq1, Eq1_RelPrePost in Hm.
      rewrite (Hm a).
      apply yoneda_at_Proper. intros b.
      apply Hk.
  Qed.

End RelPrePostMonadLaws.
