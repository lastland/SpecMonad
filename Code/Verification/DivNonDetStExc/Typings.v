(** * Triples as typings with state and exceptions

    The state-and-exceptions instances of [Generic/Typings.v]. *)

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
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Generic Require Import Typings.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.
From Incorrectness.Verification.DivNonDet Require Import DijkstraMonads.
From Incorrectness.Verification.DivNonDet Require Import Typings.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.
From Incorrectness.Verification.DivNonDetStExc Require Import DijkstraMonads.


Definition wpUnderStExc {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : WStExc S A := mkStateT (fun s => mkOptionT (wpUnderPure (pre s) post)).

Definition wpOverStExc {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : WStExc S A := mkStateT (fun s => mkOptionT (wpOverPure (pre s) post)).

(** For any morphism into the three WP monads, so for all four readings:
    an [Under] triple is a typing in [DM] at [wpUnder], an [Over] triple a
    typing in [DMop] at [wpOver]. *)
Section WPTypings.
  Context {M : Type -> Type}.

  Context {S : Type}.

  Theorem triple_under_wpStExc (θ : forall A, M A -> WStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Under pre post <-> ordWStExc (θ A m) (wpUnderStExc pre post).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpUnderPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
    - exact (proj2 (le_wpUnderPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
  Qed.

  Theorem triple_over_wpStExc (θ : forall A, M A -> WStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Over pre post <-> ordWStExc (wpOverStExc pre post) (θ A m).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpOverPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
    - exact (proj2 (le_wpOverPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
  Qed.
End WPTypings.

Section SPTypings.
  Context {M : Type -> Type}.

  Context {S : Type}.

  Theorem triple_over_aspStExc (θ : forall A, M A -> ASPStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Over pre post
    <-> ordASPStExc (θ A m)
          (aspOver (fun p : unit * S => pre (snd p)) post).
  Proof. exact (le_aspOver (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_under_dslpStExc (θ : forall A, M A -> DSLPStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Under pre post
    <-> ordDSLPStExc
          (dslpUnder (fun p : unit * S => pre (snd p)) post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) (fun p => pre (snd p)) post). Qed.
End SPTypings.
