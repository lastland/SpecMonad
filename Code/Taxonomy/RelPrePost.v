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
    - **Projection operations**: monad/arrow operations are defined
      via the helper [project_wp] (which equals [α]), so they only
      "see" the γ-image of their inputs.
    - **α-induced equivalence**: [Eq1] / [arrow_eq] identify two
      [RelPrePost] values when they have the same projection
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
(** ** Type definition and projection                                 *)
(* ================================================================= *)

Definition RelPrePost (A B : Type) : Type :=
  (A -> Prop) -> (A -> B -> Prop) -> Prop.

(** [project_wp r a Q] is the [α]-image of [r] at point [(a, Q)]: it
    holds iff [r] validates some pre/post pair whose pre contains [a]
    and whose post-row at [a] is pointwise iff [Q]. *)
Definition project_wp {A B}
  (r : RelPrePost A B) (a : A) (Q : B -> Prop) : Prop :=
  exists P R, r P R /\ P a /\ (forall b, R a b <-> Q b).

(** [project_wp] respects pointwise iff in its post argument. *)
#[global]
Instance project_wp_Proper {A B} (r : RelPrePost A B) (a : A) :
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

Definition RelPrePost_arrow_eq {A B} : RelPrePost A B -> RelPrePost A B -> Prop :=
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
Instance ArrowEq_RelPrePost : ArrowEq RelPrePost := {
  arrow_eq := @RelPrePost_arrow_eq
}.

(** DM4all refinement order: reverse pointwise implication on
    validators.  [r1 ≤ r2] iff [r2 P R → r1 P R] for all [P], [R]. *)
Definition RelPrePost_le {A B} (r1 r2 : RelPrePost A B) : Prop :=
  forall P R, r2 P R -> r1 P R.

#[global]
Instance RelPrePost_le_PreOrder {A B} : PreOrder (@RelPrePost_le A B).
Proof. constructor; cbv; auto. Qed.

#[global]
Instance Arrow_RelPrePost : Arrow RelPrePost := {
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
Instance ArrowChoice_RelPrePost : ArrowChoice RelPrePost := {
  arr_left := fun A B C r =>
    fun P R =>
      forall x, P x ->
        match x with
        | inl a => project_wp r a (fun b => R x (inl b))
        | inr c => R x (inr c)
        end
}.

#[global]
Instance ArrowApply_RelPrePost : ArrowApply RelPrePost := {
  arr_app := fun A B =>
    fun P R =>
      forall x : (RelPrePost A B * A)%type, P x ->
        let '(r, a) := x in project_wp r a (fun b => R x b)
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
        project_wp r a (fun b => project_wp (k b) a (R_AC a)).

  #[global]
  Instance Monad_RelPrePost : Monad (RelPrePost A) := {
    ret := @retRelPrePost ;
    bind := @bindRelPrePost
  }.

  #[global]
  Instance Eq1_RelPrePost : Eq1 (RelPrePost A) :=
    fun B r1 r2 =>
      forall a Q, project_wp r1 a Q <-> project_wp r2 a Q.

End RelPrePostMonad.

(* ================================================================= *)
(** ** Well-formedness subtype                                        *)
(* ================================================================= *)

(** [WFRelPrePost] is the well-formedness subtype of [RelPrePost] used
    as a Galois connection endpoint.  The well-formedness condition
    ensures the [project_wp] projection is monotone in the
    postcondition, so it lands in [MonotoneWP].

    These definitions are co-located with [RelPrePost] so the raw type
    and its well-formedness boundary live together; they were
    previously local to [Taxonomy/Galois.v]. *)
Definition RelPrePost_wf {A B} (r : RelPrePost A B) : Prop :=
  forall a Q1 Q2, (forall b, Q1 b -> Q2 b) ->
    project_wp r a Q1 -> project_wp r a Q2.

Definition WFRelPrePost (A B : Type) : Type :=
  { r : RelPrePost A B | RelPrePost_wf r }.

(** Reverse pointwise implication on validators, lifted to the
    subtype.  Mirrors [MonotoneWP_le]. *)
Definition WFRelPrePost_le {A B}
  (r1 r2 : WFRelPrePost A B) : Prop :=
  RelPrePost_le (proj1_sig r1) (proj1_sig r2).

#[global]
Instance WFRelPrePost_le_PreOrder {A B}
  : PreOrder (@WFRelPrePost_le A B).
Proof.
  constructor; unfold WFRelPrePost_le, RelPrePost_le; intros; auto.
Qed.
