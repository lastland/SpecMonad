(** * The pre/post relational arrow [PrePost].

    [PrePost A B := (A -> Prop) * (A -> B -> Prop)] packages a Hoare
    triple [{P} _ {R}] where the post-relation [R] may reference the
    initial state [a].  Making the post-relation depend on the input
    [a] (rather than just on [b]) lets [arr_pure id] hold the diagonal
    [fun a b => a = b], so a strict Hughes-style [Arrow] instance
    works without coarsening the equivalence.

    This file defines the type [PrePost], the pointwise-iff
    equivalence [PrePost_eq], the partial-correctness Hoare order
    [PrePost_le] (stronger pre, weaker post), and the [ArrowEq] /
    [Arrow] / [ArrowChoice] /
    [ArrowApply] / [Monad] / [Eq1] instances.  All the corresponding
    laws ([ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws],
    [Eq1Equivalence], [MonadLawsE]) are proved in
    [Taxonomy/PrePostFacts.v].

    Galois connections relating [PrePost] to [Pred] and [WPArr] are
    collected in [Taxonomy/Galois.v]. *)

From Coq Require Import
  Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Type definition                                                *)
(* ================================================================= *)

Definition PrePost (A B : Type) : Type :=
  ((A -> Prop) * (A -> B -> Prop))%type.

(** Pointwise iff equivalence on both components — no extensionality
    axioms required. *)
Definition PrePost_eq {A B} (pq1 pq2 : PrePost A B) : Prop :=
  (forall a, fst pq1 a <-> fst pq2 a) /\
  (forall a b, snd pq1 a b <-> snd pq2 a b).

#[global]
Instance PrePost_eq_Equivalence {A B} : Equivalence (@PrePost_eq A B).
Proof.
  constructor.
  - intros pq. split; reflexivity.
  - intros pq1 pq2 [HP HR]. split; intros; [symmetry; apply HP | symmetry; apply HR].
  - intros pq1 pq2 pq3 [HP12 HR12] [HP23 HR23]. split; intros.
    + etransitivity; [apply HP12 | apply HP23].
    + etransitivity; [apply HR12 | apply HR23].
Qed.

(** Partial-correctness Hoare order: strengthen the precondition,
    weaken the post-relation.  [pq1 ≤ pq2] iff [fst pq2 ⊆ fst pq1]
    and [snd pq1 ⊆ snd pq2].  Pairs with covariant [Pred_le] to make
    [α R := (True, R)], [γ pq := snd pq] a Galois connection (see
    [Taxonomy/Galois.v]). *)
Definition PrePost_le {A B} (pq1 pq2 : PrePost A B) : Prop :=
  (forall a,   fst pq2 a   -> fst pq1 a) /\
  (forall a b, snd pq1 a b -> snd pq2 a b).

#[global]
Instance PrePost_le_PreOrder {A B} : PreOrder (@PrePost_le A B).
Proof.
  constructor.
  - intros [P R]. split; intros; assumption.
  - intros [P1 R1] [P2 R2] [P3 R3] [HP12 HR12] [HP23 HR23].
    split; intros.
    + apply HP12, HP23. assumption.
    + apply HR23, HR12. assumption.
Qed.

(* ================================================================= *)
(** ** Arrow instances                                                *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PrePost : ArrowEq PrePost := {
  arrow_eq := @PrePost_eq
}.

#[global]
Instance Arrow_PrePost : Arrow PrePost := {
  arr_pure := fun A B f =>
    (fun _ : A => True, fun a b => f a = b) ;
  arr_comp := fun A B C pq1 pq2 =>
    ( fun a => fst pq1 a /\ (forall b, snd pq1 a b -> fst pq2 b)
    , fun a c => exists b, snd pq1 a b /\ snd pq2 b c ) ;
  arr_first := fun A B C pq =>
    ( fun p : (A * C)%type => fst pq (fst p)
    , fun p q => snd pq (fst p) (fst q) /\ snd p = snd q )
}.

#[global]
Instance ArrowChoice_PrePost : ArrowChoice PrePost := {
  arr_left := fun A B C pq =>
    ( fun x => match x with
               | inl a => fst pq a
               | inr _ => True
               end
    , fun x y => match x, y with
                 | inl a, inl b => snd pq a b
                 | inr c, inr c' => c = c'
                 | _, _ => False
                 end
    )
}.

#[global]
Instance ArrowApply_PrePost : ArrowApply PrePost := {
  arr_app := fun A B =>
    ( fun p : (PrePost A B * A)%type => fst (fst p) (snd p)
    , fun p b => snd (fst p) (snd p) b )
}.

(* ================================================================= *)
(** ** Monad instance (second argument, [A] fixed)                    *)
(* ================================================================= *)

Section PrePostMonad.

  Context {A : Type}.

  Definition retPrePost {B} (b : B) : PrePost A B :=
    (fun _ => True, fun _ b' => b = b').

  Definition bindPrePost {B C}
    (m : PrePost A B) (k : B -> PrePost A C) : PrePost A C :=
    ( fun a => fst m a /\ (forall b, snd m a b -> fst (k b) a)
    , fun a c => exists b, snd m a b /\ snd (k b) a c ).

  #[global]
  Instance Monad_PrePost : Monad (PrePost A) := {
    ret := @retPrePost ;
    bind := @bindPrePost
  }.

  #[global]
  Instance Eq1_PrePost : Eq1 (PrePost A) :=
    fun B m1 m2 =>
      (forall a,   fst m1 a   <-> fst m2 a) /\
      (forall a b, snd m1 a b <-> snd m2 a b).

End PrePostMonad.

(** Galois connections with other spec types are collected in
    [Taxonomy/Galois.v]. *)
