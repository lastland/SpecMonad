(** * Triples as typings without state

    The base instances of [Generic/Typings.v].  Without state there is one
    start point, the two readings of an ASP [Under] triple agree, and the
    triple is a typing ([triple_under_aspPure]); [oneOrTwo_Dasp_op] is an
    example. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow ArrowMonad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Relational Require Import Rel.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Coq Require Import Lia PeanoNat Classical_Prop.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Generic Require Import Typings.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.
From Incorrectness.Verification.DivNonDet Require Import DijkstraMonads.


Definition wpUnderPure {A} (pre : Prop) (post : A -> Prop) : WPure A :=
  mkWPure _ (wpUnder_mono pre post).

Definition wpOverPure {A} (pre : Prop) (post : A -> Prop) : WPure A :=
  mkWPure _ (wpOver_mono pre post).

Lemma le_wpUnderPure {A} (w : WPure A) (pre : Prop) (post : A -> Prop) :
  (pre -> getWPure w post) <-> WP_le w (wpUnderPure pre post).
Proof.
  split.
  - intros H k [Hpre Hsub]. exact (getWPure_mono w post k Hsub (H Hpre)).
  - intros H Hpre. exact (H post (conj Hpre (fun a Ha => Ha))).
Qed.

Lemma le_wpOverPure {A} (w : WPure A) (pre : Prop) (post : A -> Prop) :
  (getWPure w post -> pre) <-> WP_le (wpOverPure pre post) w.
Proof.
  split.
  - intros H k Hk Hsub. exact (H (getWPure_mono w k post Hsub Hk)).
  - intros H Hw. exact (H post Hw (fun a Ha => Ha)).
Qed.

(** For any morphism into the three WP monads, so for all four readings:
    an [Under] triple is a typing in [DM] at [wpUnder], an [Over] triple a
    typing in [DMop] at [wpOver]. *)
Section WPTypings.
  Context {M : Type -> Type}.

  Theorem triple_under_wpPure (θ : forall A, M A -> WPure A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Under pre post
    <-> WP_le (θ A m) (wpUnderPure (pre tt) post).
  Proof.
    etransitivity; [| exact (le_wpUnderPure (θ A m) (pre tt) post) ].
    split; [ intros H Hp; exact (H tt Hp) | intros H [] Hp; exact (H Hp) ].
  Qed.

  Theorem triple_over_wpPure (θ : forall A, M A -> WPure A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Over pre post
    <-> WP_le (wpOverPure (pre tt) post) (θ A m).
  Proof.
    etransitivity; [| exact (le_wpOverPure (θ A m) (pre tt) post) ].
    split; [ intros H Hw; exact (H tt Hw) | intros H [] Hw; exact (H Hw) ].
  Qed.

  Context {S : Type}.
End WPTypings.

Section SPTypings.
  Context {M : Type -> Type}.

  Theorem triple_over_aspPure (θ : forall A, M A -> ASP A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Over pre post <-> ordASP (θ A m) (aspOver pre post).
  Proof. exact (le_aspOver (θ A m) pre post). Qed.

  Theorem triple_under_dslpPure (θ : forall A, M A -> DSLP A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Under pre post <-> ordDSLP (dslpUnder pre post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) pre post). Qed.

  Context {S : Type}.
End SPTypings.

Theorem triple_under_aspPure {M : Type -> Type} (θ : forall A, M A -> ASP A)
  {Hθ : IsMonadMorphism θ} {A} (m : M A)
  (pre : unit -> Prop) (post : A -> Prop) :
  pre tt ->
  (triple θ m Under pre post <-> ordASP (aspUnder pre post) (θ A m)).
Proof. exact (le_aspUnder_unit (θ A m) pre post). Qed.

(* ================================================================= *)
(** * Without state                                                   *)
(* ================================================================= *)

(** A computation with no state that returns [1] or [2]. *)
Definition oneOrTwo : divndNE nat := orNE (retNE 1) (retNE 2).

Theorem oneOrTwo_asp_under :
  triple (@aspPure) oneOrTwo Under (fun _ => True) (fun a => a = 1).
Proof.
  intros a Ha. subst a. exists tt. split; [ exact I |].
  cbn. left. reflexivity.
Qed.

(** The triple is a typing: there is one start point. *)
Definition oneOrTwo_Dasp_op :
  DMop (@aspPure) (@ordASP)
    (aspUnder (fun _ : unit => True) (fun a : nat => a = 1)) :=
  exist _ oneOrTwo
    (proj1 (triple_under_aspPure (@aspPure) oneOrTwo _ _ I)
       oneOrTwo_asp_under).
