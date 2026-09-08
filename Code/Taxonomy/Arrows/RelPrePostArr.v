(** * The predicate-on-Hoare-specs type [RelPrePostArr].

    [RelPrePostArr A B := (A -> Prop) -> (A -> B -> Prop) -> Prop] is a
    "validator" of Hoare-style pre/post specs.

    The natural [γ : WPArr → RelPrePostArr] is an injective embedding
    (with [α : RelPrePostArr → WPArr] as its left inverse, [α ∘ γ = id]),
    so [RelPrePostArr] is strictly larger than [WPArr]: it includes "wild"
    predicates over [PrePostArr] that don't correspond to any
    weakest-precondition transformer.

    To get lawful [Arrow] and [Monad] instances on the *whole*
    [RelPrePostArr] type (not just the γ-image), we use:
    - **Projection operations**: monad/arrow operations are defined
      via the helper [project_wp] (which equals [α]), so they only
      "see" the γ-image of their inputs.
    - **α-induced equivalence**: [Eq1] / [arrow_eq] identify two
      [RelPrePostArr] values when they have the same projection
      behavior — equivalently, when their [α] images coincide.

    Under this equivalence, every [RelPrePostArr] value is identified
    with its [γ ∘ α] closure (a γ-image), and the operations cleanly
    inherit all laws from [WPArr]'s [Arrow] / [Monad].

    This file holds the type definition and all [Arrow] / [ArrowChoice]
    / [ArrowApply] / [Monad] / [Eq1] instances.  All the corresponding
    laws are proved in [Taxonomy/RelPrePostArr.v]. *)

From Coq Require Import FunctionalExtensionality PropExtensionality Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Type definition and projection                                 *)
(* ================================================================= *)

Definition RelPrePostArr (A B : Type) : Type :=
  (A -> Prop) -> (A -> B -> Prop) -> Prop.

(** [project_wp r a Q] is the [α]-image of [r] at point [(a, Q)]: it
    holds iff [r] validates some pre/post pair whose pre contains [a]
    and whose post-row at [a] is pointwise iff [Q]. *)
Definition project_wp {A B}
  (r : RelPrePostArr A B) (a : A) (Q : B -> Prop) : Prop :=
  exists P R, r P R /\ P a /\ (forall b, R a b <-> Q b).

(** [project_wp] respects pointwise iff in its post argument. *)
#[global]
Instance project_wp_Proper {A B} (r : RelPrePostArr A B) (a : A) :
  Proper (pointwise_relation B iff ==> iff) (project_wp r a).
Proof.
  intros Q1 Q2 HQ. unfold project_wp.
  split; intros [P [R [HPR [HPa Hiff]]]];
    exists P, R; (split; [exact HPR | split; [exact HPa|]]);
    intros b; specialize (HQ b); specialize (Hiff b); tauto.
Qed.

(* ================================================================= *)
(** ** Arrow instances                                                *)
(* ================================================================= *)

Definition RelPrePost_arrow_eq {A B} : RelPrePostArr A B -> RelPrePostArr A B -> Prop :=
  fun r1 r2 => forall a Q, project_wp r1 a Q <-> project_wp r2 a Q.

#[global]
Instance RelPrePost_arrow_eq_Equivalence {A B}
  : Equivalence (@RelPrePost_arrow_eq A B).
Proof.
  constructor.
  - intros r a Q. reflexivity.
  - intros r1 r2 H a Q. symmetry. apply H.
  - intros r1 r2 r3 H12 H23 a Q. etransitivity; [apply H12 | apply H23].
Qed.

#[global]
Instance ArrowEq_RelPrePost : ArrowEq RelPrePostArr := {
  arrow_eq := @RelPrePost_arrow_eq
}.

(** DM4all refinement order: reverse pointwise implication on
    validators.  [r1 ≤ r2] iff [r2 P R → r1 P R] for all [P], [R]. *)
Definition RelPrePost_le {A B} (r1 r2 : RelPrePostArr A B) : Prop :=
  forall P R, r2 P R -> r1 P R.

#[global]
Instance RelPrePost_le_PreOrder {A B} : PreOrder (@RelPrePost_le A B).
Proof. constructor; cbv; auto. Qed.

#[global]
Instance Arrow_RelPrePost : Arrow RelPrePostArr := {
  arr_pure := fun A B f =>
    fun P R => forall a, P a -> R a (f a) ;
  arr_comp := fun A B C r s =>
    fun P R_AC =>
      forall a, P a ->
        project_wp r a (fun b => project_wp s b (R_AC a)) ;
  arr_first := fun A B C r =>
    fun P R =>
      forall p, P p ->
        project_wp r (fst p) (fun b => R p (b, snd p))
}.

#[global]
Instance ArrowChoice_RelPrePost : ArrowChoice RelPrePostArr := {
  arr_left := fun A B C r =>
    fun P R =>
      forall x, P x ->
        match x with
        | inl a => project_wp r a (fun b => R x (inl b))
        | inr c => R x (inr c)
        end
}.

#[global]
Instance ArrowApply_RelPrePost : ArrowApply RelPrePostArr := {
  arr_app := fun A B =>
    fun P R =>
      forall x : (RelPrePostArr A B * A)%type, P x ->
        let '(r, a) := x in project_wp r a (fun b => R x b)
}.

(* ================================================================= *)
(** ** Monad instance (in [B] for fixed [A])                          *)
(* ================================================================= *)

Section RelPrePostMonad.

  Context {A : Type}.

  Definition retRelPrePost {B} (b : B) : RelPrePostArr A B :=
    fun P R => forall a, P a -> R a b.

  Definition bindRelPrePost {B C}
    (r : RelPrePostArr A B) (k : B -> RelPrePostArr A C) : RelPrePostArr A C :=
    fun P R_AC =>
      forall a, P a ->
        project_wp r a (fun b => project_wp (k b) a (R_AC a)).

  #[global]
  Instance Monad_RelPrePost : Monad (RelPrePostArr A) := {
    ret := @retRelPrePost ;
    bind := @bindRelPrePost
  }.

  #[global]
  Instance Eq1_RelPrePost : Eq1 (RelPrePostArr A) :=
    fun B r1 r2 =>
      forall a Q, project_wp r1 a Q <-> project_wp r2 a Q.

End RelPrePostMonad.

(* ================================================================= *)
(** * Facts and laws (merged from RelPrePostArrFacts.v)                          *)
(* ================================================================= *)

(** * Laws for [RelPrePostArr].

    This file collects the projection characterization lemmas
    ([project_wp_arr_pure], [project_wp_arr_comp], etc.) and proves
    [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws], [Eq1Equivalence]
    and [MonadLawsE] for [RelPrePostArr]. *)

From Coq Require Import FunctionalExtensionality PropExtensionality Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.


(* ================================================================= *)
(** ** Projection characterization lemmas                           *)
(* ================================================================= *)

(** [project_wp] of an arrow operation reduces to a clean formula. *)

Lemma project_wp_arr_pure {A B} (f : A -> B) (a : A) (Q : B -> Prop) :
  project_wp (@arr_pure _ Arrow_RelPrePost A B f) a Q <-> Q (f a).
Proof.
  unfold project_wp; cbn. split.
  - intros [P [R [HPR [HPa Hiff]]]]. apply Hiff. apply HPR. exact HPa.
  - intros HQ. exists (eq a), (fun a' b => a' = a -> Q b). split; [|split].
    + intros a' Heq. subst a'. intros _. exact HQ.
    + reflexivity.
    + intros b. split; [intros H; apply H; reflexivity | intros HQb _; exact HQb].
Qed.

Lemma project_wp_arr_comp {A B C} (r : RelPrePostArr A B) (s : RelPrePostArr B C)
  (a : A) (Q : C -> Prop) :
  project_wp (@arr_comp _ Arrow_RelPrePost A B C r s) a Q
  <-> project_wp r a (fun b => project_wp s b Q).
Proof.
  unfold project_wp at 1; cbn. split.
  - intros [P [R [HPR [HPa Hiff]]]].
    specialize (HPR a HPa).
    (* HPR : project_wp r a (fun b => project_wp s b (R a))
       Goal : project_wp r a (fun b => project_wp s b Q)
       Use Proper of project_wp to swap (R a) with Q via Hiff. *)
    enough (Hyo : project_wp r a (fun b => project_wp s b (R a))
                  <-> project_wp r a (fun b => project_wp s b Q))
      by (apply Hyo; exact HPR).
    apply project_wp_Proper. intros b.
    apply project_wp_Proper. exact Hiff.
  - intros Hr.
    exists (eq a), (fun a' c => a' = a -> Q c).
    split; [|split].
    + intros a' Heq. subst a'.
      enough (Hyo : project_wp r a (fun b => project_wp s b Q)
                    <-> project_wp r a (fun b => project_wp s b (fun c => a = a -> Q c)))
        by (apply Hyo; exact Hr).
      apply project_wp_Proper. intros b.
      apply project_wp_Proper. intros c. tauto.
    + reflexivity.
    + intros c. tauto.
Qed.

Lemma project_wp_arr_left {A B C} (r : RelPrePostArr A B)
  (x : A + C) (Q : (B + C) -> Prop) :
  project_wp (@arr_left _ _ _ A B C r) x Q
  <-> match x with
      | inl a => project_wp r a (fun b => Q (inl b))
      | inr c => Q (inr c)
      end.
Proof.
  unfold project_wp at 1; cbn. split.
  - intros [P [R [HPR [HPx Hiff]]]].
    specialize (HPR x HPx).
    destruct x as [a|c].
    + (* inl a *)
      enough (Hyo : project_wp r a (fun b => R (inl a) (inl b))
                    <-> project_wp r a (fun b => Q (inl b)))
        by (apply Hyo; exact HPR).
      apply project_wp_Proper. intros b. apply (Hiff (inl b)).
    + (* inr c *)
      apply (proj1 (Hiff (inr c))). exact HPR.
  - destruct x as [a|c]; intros H.
    + (* inl a *)
      exists (eq (inl a)), (fun x' y => x' = inl a -> Q y).
      split; [|split].
      * intros x' Heq. subst x'. cbn.
        enough (Hyo : project_wp r a (fun b => Q (inl b))
                      <-> project_wp r a (fun b => inl a = inl a -> Q (inl b)))
          by (apply Hyo; exact H).
        apply project_wp_Proper. intros b. tauto.
      * reflexivity.
      * intros y. tauto.
    + (* inr c *)
      exists (eq (inr c)), (fun x' y => x' = inr c -> Q y).
      split; [|split].
      * intros x' Heq. subst x'. cbn. intros _. exact H.
      * reflexivity.
      * intros y. tauto.
Qed.

Lemma project_wp_arr_app {A B}
  (x : (RelPrePostArr A B * A)%type) (Q : B -> Prop) :
  project_wp (@arr_app _ _ ArrowApply_RelPrePost A B) x Q
  <-> (let '(r, a) := x in project_wp r a Q).
Proof.
  unfold project_wp at 1; cbn. split.
  - intros [P [R [HPR [HPx Hiff]]]].
    specialize (HPR x HPx).
    destruct x as [r a]. cbn in HPR.
    enough (Hyo : project_wp r a (fun b => R (r, a) b)
                  <-> project_wp r a Q)
      by (apply Hyo; exact HPR).
    apply project_wp_Proper. intros b. apply Hiff.
  - destruct x as [r a]. intros H.
    exists (eq (r, a)), (fun x' y => x' = (r, a) -> Q y).
    split; [|split].
    + intros x' Heq. subst x'. cbn.
      enough (Hyo : project_wp r a Q
                    <-> project_wp r a (fun b => (r, a) = (r, a) -> Q b))
        by (apply Hyo; exact H).
      apply project_wp_Proper. intros b. tauto.
    + reflexivity.
    + intros y. tauto.
Qed.

Lemma project_wp_arr_first {A B C} (r : RelPrePostArr A B)
  (p : A * C) (Q : B * C -> Prop) :
  project_wp (@arr_first _ Arrow_RelPrePost A B C r) p Q
  <-> project_wp r (fst p) (fun b => Q (b, snd p)).
Proof.
  unfold project_wp at 1; cbn. split.
  - intros [P [R [HPR [HPp Hiff]]]].
    specialize (HPR p HPp).
    enough (Hyo : project_wp r (fst p) (fun b => R p (b, snd p))
                  <-> project_wp r (fst p) (fun b => Q (b, snd p)))
      by (apply Hyo; exact HPR).
    apply project_wp_Proper. intros b. apply (Hiff (b, snd p)).
  - intros Hr.
    exists (eq p), (fun p' bc => p' = p -> Q bc).
    split; [|split].
    + intros p' Heq. subst p'.
      enough (Hyo : project_wp r (fst p) (fun b => Q (b, snd p))
                    <-> project_wp r (fst p) (fun b => p = p -> Q (b, snd p)))
        by (apply Hyo; exact Hr).
      apply project_wp_Proper. intros b. tauto.
    + reflexivity.
    + intros bc. tauto.
Qed.

(** Specialized versions of [project_wp_arr_left] that handle [inl] and
    [inr] without a match.  Convenient for [rewrite]. *)
Lemma project_wp_arr_left_inl {A B C} (r : RelPrePostArr A B)
  (a : A) (Q : (B + C) -> Prop) :
  project_wp (@arr_left _ _ _ A B C r) (inl a) Q
  <-> project_wp r a (fun b => Q (inl b)).
Proof. rewrite project_wp_arr_left. reflexivity. Qed.

Lemma project_wp_arr_left_inr {A B C} (r : RelPrePostArr A B)
  (c : C) (Q : (B + C) -> Prop) :
  project_wp (@arr_left _ _ _ A B C r) (inr c) Q
  <-> Q (inr c).
Proof. rewrite project_wp_arr_left. reflexivity. Qed.

(** Specialized version of [project_wp_arr_first] that takes a destructured
    pair, avoiding unreduced [fst]/[snd]. *)
Lemma project_wp_arr_first_pair {A B C} (r : RelPrePostArr A B)
  (a : A) (c : C) (Q : B * C -> Prop) :
  project_wp (@arr_first _ Arrow_RelPrePost A B C r) (a, c) Q
  <-> project_wp r a (fun b => Q (b, c)).
Proof. rewrite project_wp_arr_first. reflexivity. Qed.

(* ================================================================= *)
(** ** Arrow laws                                                     *)
(* ================================================================= *)

#[global]
Instance ArrowLaws_RelPrePost : ArrowLaws RelPrePostArr.
Proof.
  constructor; intros.
  - (* comp_id_l: arr_comp arr_id f ≡ f *)
    intros a Q. rewrite project_wp_arr_comp.
    unfold arr_id. setoid_rewrite project_wp_arr_pure.
    reflexivity.
  - (* comp_id_r: arr_comp f arr_id ≡ f *)
    intros a Q. rewrite project_wp_arr_comp.
    unfold arr_id.
    apply project_wp_Proper. intros b. rewrite project_wp_arr_pure.
    reflexivity.
  - (* comp_assoc *)
    intros a Q. rewrite !project_wp_arr_comp.
    apply project_wp_Proper. intros b. rewrite project_wp_arr_comp.
    reflexivity.
  - (* pure_comp *)
    intros a Q. rewrite project_wp_arr_comp, !project_wp_arr_pure.
    reflexivity.
  - (* first_pure *)
    intros p Q. rewrite project_wp_arr_first, !project_wp_arr_pure.
    destruct p as [a c]; cbn. reflexivity.
  - (* first_comp *)
    intros p Q.
    rewrite project_wp_arr_first.
    rewrite project_wp_arr_comp.
    rewrite project_wp_arr_comp.
    rewrite project_wp_arr_first.
    apply project_wp_Proper. intros b.
    rewrite project_wp_arr_first.
    destruct p as [a d]; cbn. reflexivity.
  - (* first_fst *)
    intros p Q.
    rewrite project_wp_arr_comp.
    rewrite project_wp_arr_first.
    rewrite project_wp_arr_comp.
    setoid_rewrite project_wp_arr_pure.
    destruct p as [a c]; cbn.
    reflexivity.
  - (* first_assoc *)
    intros p Q.
    rewrite project_wp_arr_comp.
    rewrite project_wp_arr_first.
    rewrite project_wp_arr_first.
    rewrite project_wp_arr_comp.
    setoid_rewrite project_wp_arr_pure.
    setoid_rewrite project_wp_arr_first.
    destruct p as [[a c] d]; cbn.
    unfold assoc_prod; cbn.
    reflexivity.
  - (* comp_proper *)
    intros r1 r2 Hr s1 s2 Hs a Q.
    rewrite !project_wp_arr_comp.
    rewrite (Hr a). apply project_wp_Proper. intros b. apply Hs.
  - (* first_proper *)
    intros r1 r2 Hr p Q.
    rewrite !project_wp_arr_first.
    apply Hr.
Qed.

#[global]
Instance ArrowChoiceLaws_RelPrePost : ArrowChoiceLaws RelPrePostArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    intros x Q. destruct x as [a|c].
    + rewrite project_wp_arr_left_inl, !project_wp_arr_pure.
      unfold sum_bimap. reflexivity.
    + rewrite project_wp_arr_left_inr, project_wp_arr_pure.
      unfold sum_bimap. reflexivity.
  - (* left_comp *)
    intros x Q. destruct x as [a|c].
    + rewrite project_wp_arr_left_inl, !project_wp_arr_comp.
      rewrite project_wp_arr_left_inl. cbv beta.
      setoid_rewrite project_wp_arr_left_inl.
      reflexivity.
    + rewrite project_wp_arr_left_inr, project_wp_arr_comp.
      rewrite project_wp_arr_left_inr. cbv beta.
      rewrite project_wp_arr_left_inr. reflexivity.
  - (* left_inl *)
    intros a Q.
    rewrite !project_wp_arr_comp.
    setoid_rewrite project_wp_arr_pure.
    rewrite project_wp_arr_left_inl.
    reflexivity.
  - (* left_assoc *)
    intros x Q.
    rewrite !project_wp_arr_comp.
    setoid_rewrite project_wp_arr_pure.
    destruct x as [[a|c]|d].
    + (* inl (inl a) *)
      rewrite project_wp_arr_left_inl. cbv beta.
      rewrite project_wp_arr_left_inl. cbv beta.
      unfold assoc_sum; cbv iota.
      rewrite project_wp_arr_left_inl.
      reflexivity.
    + (* inl (inr c) *)
      rewrite project_wp_arr_left_inl. cbv beta.
      rewrite project_wp_arr_left_inr. cbv beta.
      unfold assoc_sum; cbv iota.
      rewrite project_wp_arr_left_inr.
      reflexivity.
    + (* inr d *)
      rewrite project_wp_arr_left_inr. cbv beta.
      unfold assoc_sum; cbv iota.
      rewrite project_wp_arr_left_inr.
      reflexivity.
  - (* left_inr *)
    intros c Q.
    rewrite project_wp_arr_comp.
    setoid_rewrite project_wp_arr_pure.
    cbv beta.
    rewrite project_wp_arr_left_inr.
    reflexivity.
  - (* left_natural *)
    intros x Q.
    rewrite !project_wp_arr_comp.
    setoid_rewrite project_wp_arr_pure.
    destruct x as [a|c].
    + (* inl a *)
      rewrite project_wp_arr_left_inl. cbv beta.
      unfold sum_bimap; cbv iota.
      rewrite project_wp_arr_left_inl.
      reflexivity.
    + (* inr c *)
      rewrite project_wp_arr_left_inr. cbv beta.
      unfold sum_bimap; cbv iota.
      rewrite project_wp_arr_left_inr.
      reflexivity.
  - (* first_left_dist *)
    intros p Q.
    destruct p as [x d].
    rewrite !project_wp_arr_comp.
    rewrite project_wp_arr_first_pair.
    setoid_rewrite project_wp_arr_pure.
    destruct x as [a|c].
    + (* inl a *)
      rewrite project_wp_arr_left_inl. cbv beta.
      unfold sum_prod_dist; cbv iota.
      rewrite project_wp_arr_left_inl.
      rewrite project_wp_arr_first_pair.
      reflexivity.
    + (* inr c *)
      rewrite project_wp_arr_left_inr. cbv beta.
      unfold sum_prod_dist; cbv iota.
      rewrite project_wp_arr_left_inr.
      reflexivity.
  - (* left_proper *)
    intros r1 r2 Hr x Q. destruct x as [a|c].
    + rewrite !project_wp_arr_left_inl. apply Hr.
    + rewrite !project_wp_arr_left_inr. reflexivity.
Qed.

#[global]
Instance ArrowApplyLaws_RelPrePost : ArrowApplyLaws RelPrePostArr.
Proof.
  constructor; intros.
  (* app_law: arr_comp (arr_pure (fun a => (f, a))) arr_app ≡ f *)
  intros a Q.
  rewrite project_wp_arr_comp, project_wp_arr_pure.
  rewrite project_wp_arr_app.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Monad laws                                                     *)
(* ================================================================= *)

Section RelPrePostMonadLaws.

  Context {A : Type}.

  #[global]
  Instance Eq1Equivalence_RelPrePost
    : @Eq1Equivalence (RelPrePostArr A) _ Eq1_RelPrePost.
  Proof.
    intros B; constructor.
    - intros r a Q. reflexivity.
    - intros r1 r2 H a Q. symmetry. apply H.
    - intros r1 r2 r3 H12 H23 a Q. etransitivity; [apply H12 | apply H23].
  Qed.

  Lemma project_wp_ret {B} (b : B) (a : A) (Q : B -> Prop) :
    project_wp (retRelPrePost b) a Q <-> Q b.
  Proof.
    unfold project_wp, retRelPrePost. split.
    - intros [P [R [HPR [HPa Hiff]]]]. apply Hiff. apply HPR. exact HPa.
    - intros HQ. exists (eq a), (fun a' b' => a' = a -> Q b'). split; [|split].
      + intros a' Heq. subst a'. intros _. exact HQ.
      + reflexivity.
      + intros b'. split; [intros H; apply H; reflexivity | intros HQb _; exact HQb].
  Qed.

  Lemma project_wp_bind {B C}
    (r : RelPrePostArr A B) (k : B -> RelPrePostArr A C) (a : A) (Q : C -> Prop) :
    project_wp (bindRelPrePost r k) a Q
    <-> project_wp r a (fun b => project_wp (k b) a Q).
  Proof.
    unfold project_wp at 1, bindRelPrePost. split.
    - intros [P [R [HPR [HPa Hiff]]]].
      specialize (HPR a HPa).
      enough (Hyo : project_wp r a (fun b => project_wp (k b) a (R a))
                    <-> project_wp r a (fun b => project_wp (k b) a Q))
        by (apply Hyo; exact HPR).
      apply project_wp_Proper. intros b.
      apply project_wp_Proper. exact Hiff.
    - intros Hr.
      exists (eq a), (fun a' c => a' = a -> Q c).
      split; [|split].
      + intros a' Heq. subst a'.
        enough (Hyo : project_wp r a (fun b => project_wp (k b) a Q)
                      <-> project_wp r a (fun b => project_wp (k b) a (fun c => a = a -> Q c)))
          by (apply Hyo; exact Hr).
        apply project_wp_Proper. intros b.
        apply project_wp_Proper. intros c. tauto.
      + reflexivity.
      + intros c. tauto.
  Qed.

  #[global]
  Instance MonadLawsE_RelPrePost
    : @MonadLawsE (RelPrePostArr A) Eq1_RelPrePost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros B C f x.
      intros a Q. cbn. rewrite project_wp_bind, project_wp_ret. reflexivity.
    - (* bind_ret_r *)
      intros B m. intros a Q. cbn. rewrite project_wp_bind.
      setoid_rewrite project_wp_ret. reflexivity.
    - (* bind_bind *)
      intros B C D m f g.
      intros a Q. cbn. rewrite !project_wp_bind.
      setoid_rewrite project_wp_bind. reflexivity.
    - (* Proper_bind *)
      intros B C m1 m2 Hm k1 k2 Hk a Q. cbn.
      rewrite !project_wp_bind.
      unfold eq1, Eq1_RelPrePost in Hm.
      rewrite (Hm a).
      apply project_wp_Proper. intros b.
      apply Hk.
  Qed.

End RelPrePostMonadLaws.
