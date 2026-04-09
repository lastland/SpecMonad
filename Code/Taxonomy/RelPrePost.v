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
    inherit all laws from [WPArr]'s [Arrow] / [Monad].

    This file holds the type definition and all [Arrow] / [ArrowChoice]
    / [ArrowApply] / [Monad] / [Eq1] instances.  All the corresponding
    laws are proved in [Taxonomy/RelPrePostFacts.v]. *)

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
(** ** Arrow instances                                                *)
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

#[global]
Instance ArrowChoice_RelPrePost : ArrowChoice RelPrePost := {
  arr_left := fun A B C r =>
    fun P R =>
      forall x, P x ->
        match x with
        | inl a => yoneda_at r a (fun b => R x (inl b))
        | inr c => R x (inr c)
        end
}.

#[global]
Instance ArrowApply_RelPrePost : ArrowApply RelPrePost := {
  arr_app := fun A B =>
    fun P R =>
      forall x : (RelPrePost A B * A)%type, P x ->
        let '(r, a) := x in yoneda_at r a (fun b => R x b)
}.

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

End RelPrePostMonad.
