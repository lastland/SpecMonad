(** * The Dijkstra monads with state

    The [OrderedTarget] instances of the lifted WP, ASP and DSLP morphisms:
    the natural orders of their targets are the lifts of the base orders.
    A typing through a lifted WP morphism is a family of base typings, one
    per start state ([wpSt_typing_pointwise]). *)

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
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Base Require Import DivNonDetNE.
From Incorrectness.Verification.Base Require Import MorphismsPure.
From Incorrectness.Verification.Base Require Import DijkstraPure.
From Incorrectness.Verification.State Require Import ComputationSt.
From Incorrectness.Verification.State Require Import MorphismsSt.


#[global] Instance OrderedTarget_dwpSt (S : Type) :
  OrderedTarget (@dwpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_dwlpSt (S : Type) :
  OrderedTarget (@dwlpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwlpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_awpSt (S : Type) :
  OrderedTarget (@awpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_awlpSt (S : Type) :
  OrderedTarget (@awlpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awlpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_aspSt (S : Type) :
  OrderedTarget (@aspSt S) (@ordASPSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_aspSt S) _
    (Eq1Equivalence_ASPSt S)
    (OrderedMonad_ASPSt S).

#[global] Instance OrderedTarget_dslpSt (S : Type) :
  OrderedTarget (@dslpSt S) (@ordDSLPSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dslpSt S) _
    (Eq1Equivalence_DSLPSt S)
    (OrderedMonad_DSLPSt S).

(** A typing through a lifted WP morphism is a family of typings through the
    base morphism, one per start state. *)
Lemma wpSt_typing_pointwise {S A} (σ : forall A, divndNE A -> WPure A)
  (m : stdivndNE S A) (w : WSt S A) :
  ordWSt (stateT_map S σ A m) w
  <-> forall s, WP_le (σ _ (runStateT m s)) (runStateT w s).
Proof. reflexivity. Qed.
