(** * The predicate-on-Hoare-specs type [RelPrePost].

    [RelPrePost A B := (A -> Prop) -> (A -> B -> Prop) -> Prop] is a
    "validator" of Hoare-style pre/post specs. 

    The natural [γ : WPArr → RelPrePost] is an injective embedding
    (with [α : RelPrePost → WPArr] as its left inverse, [α ∘ γ = id]),
    so [RelPrePost] is strictly larger than [WPArr]: it includes "wild"
    predicates over [PrePost] that don't correspond to any
    weakest-precondition transformer.

    To get lawful [Arrow] and [Monad] instances on the *whole*
    [RelPrePost] type (not just the γ-image), we use:
    - **Yoneda-probe operations**: monad/arrow operations are defined
      via the helper [yoneda_at] (which equals [α]), so they only
      "see" the γ-image of their inputs.
    - **α-induced equivalence**: [Eq1] / [arrow_eq] identify two
      [RelPrePost] values when they have the same Yoneda-probe
      behavior — equivalently, when their [α] images coincide.

    Under this equivalence, every [RelPrePost] value is identified
    with its [γ ∘ α] closure (a γ-image), and the operations cleanly
    inherit all laws from [WPArr]'s [Arrow] / [Monad]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Type definition and Yoneda probe                               *)
(* ================================================================= *)

Definition RelPrePost (A B : Type) : Type :=
  (A -> Prop) -> (A -> B -> Prop) -> Prop.

(** [yoneda_at r a Q] is the [α]-image of [r] at point [(a, Q)]: it
    holds iff [r] validates some pre/post pair whose pre contains [a]
    and whose post-row at [a] is pointwise iff [Q]. *)
Definition yoneda_at {A B}
  (r : RelPrePost A B) (a : A) (Q : B -> Prop) : Prop :=
  exists P R, r P R /\ P a /\ (forall b, R a b <-> Q b).

(** [yoneda_at] respects pointwise iff in its post argument. *)
#[global]
Instance yoneda_at_Proper {A B} (r : RelPrePost A B) (a : A) :
  Proper (pointwise_relation B iff ==> iff) (yoneda_at r a).
Proof.
  intros Q1 Q2 HQ. unfold yoneda_at.
  split; intros [P [R [HPR [HPa Hiff]]]];
    exists P, R; (split; [exact HPR | split; [exact HPa|]]);
    intros b; specialize (HQ b); specialize (Hiff b); tauto.
Qed.

(* ================================================================= *)
(** ** Arrow instance                                                 *)
(* ================================================================= *)

Definition RelPrePost_arrow_eq {A B} : RelPrePost A B -> RelPrePost A B -> Prop :=
  fun r1 r2 => forall a Q, yoneda_at r1 a Q <-> yoneda_at r2 a Q.

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
Instance ArrowEq_RelPrePost : ArrowEq RelPrePost := {
  arrow_eq := @RelPrePost_arrow_eq
}.

#[global]
Instance Arrow_RelPrePost : Arrow RelPrePost := {
  arr_pure := fun A B f =>
    fun P R => forall a, P a -> R a (f a) ;
  arr_comp := fun A B C r s =>
    fun P R_AC =>
      forall a, P a ->
        yoneda_at r a (fun b => yoneda_at s b (R_AC a)) ;
  arr_first := fun A B C r =>
    fun P R =>
      forall p, P p ->
        yoneda_at r (fst p) (fun b => R p (b, snd p))
}.

(** Yoneda-probe characterization lemmas: [yoneda_at] of an arrow
    operation reduces to a clean formula. *)

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

(** [yoneda_at] of an arrow [r] applied to a [pointwise_relation]-equal
    function in [Q] gives the same value.  This is essentially
    [yoneda_at_Proper] re-stated for use as a rewrite rule. *)

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

(* ================================================================= *)
(** ** Monad instance (in [B] for fixed [A])                          *)
(* ================================================================= *)

Section RelPrePostMonad.

  Context {A : Type}.

  Definition retRelPrePost {B} (b : B) : RelPrePost A B :=
    fun P R => forall a, P a -> R a b.

  Definition bindRelPrePost {B C}
    (r : RelPrePost A B) (k : B -> RelPrePost A C) : RelPrePost A C :=
    fun P R_AC =>
      forall a, P a ->
        yoneda_at r a (fun b => yoneda_at (k b) a (R_AC a)).

  #[global]
  Instance Monad_RelPrePost : Monad (RelPrePost A) := {
    ret := @retRelPrePost ;
    bind := @bindRelPrePost
  }.

  #[global]
  Instance Eq1_RelPrePost : Eq1 (RelPrePost A) :=
    fun B r1 r2 =>
      forall a Q, yoneda_at r1 a Q <-> yoneda_at r2 a Q.

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

End RelPrePostMonad.
