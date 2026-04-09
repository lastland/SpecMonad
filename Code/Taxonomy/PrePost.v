(** * The pre/post relational arrow [PrePost].

    [PrePost A B := (A -> Prop) * (A -> B -> Prop)] packages a Hoare
    triple [{P} _ {R}] where the post-relation [R] may reference the
    initial state [a].  Making the post-relation depend on the input
    [a] (rather than just on [b]) lets [arr_pure id] hold the diagonal
    [fun a b => a = b], so a strict Hughes-style [Arrow] instance
    works without coarsening the equivalence.

    This file defines the type [PrePost], the [PrePost_eq] helper
    (bridging pointwise iff to structural equality via funext +
    propext), and the [ArrowEq] / [Arrow] / [ArrowChoice] /
    [ArrowApply] / [Monad] / [Eq1] instances.  All the corresponding
    laws ([ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws],
    [Eq1Equivalence], [MonadLawsE]) are proved in
    [Taxonomy/PrePostFacts.v].

    Galois connections relating [PrePost] to [Pred] and [WPArr] are
    collected in [Taxonomy/Galois.v]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Type definition                                                *)
(* ================================================================= *)

Definition PrePost (A B : Type) : Type :=
  ((A -> Prop) * (A -> B -> Prop))%type.

Lemma PrePost_eq {A B} (pq1 pq2 : PrePost A B) :
  (forall a, fst pq1 a <-> fst pq2 a) ->
  (forall a b, snd pq1 a b <-> snd pq2 a b) ->
  pq1 = pq2.
Proof.
  destruct pq1 as [P1 R1]; destruct pq2 as [P2 R2]; simpl; intros HP HR.
  f_equal.
  - extensionality a. apply propositional_extensionality, HP.
  - extensionality a. extensionality b.
    apply propositional_extensionality, HR.
Qed.

(* ================================================================= *)
(** ** Arrow instances                                                *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PrePost : ArrowEq PrePost := {
  arrow_eq := fun A B => @eq (PrePost A B)
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
