(** * The Dijkstra monads with state and exceptions

    The [OrderedTarget] instances of the lifted morphisms, and the twelve
    named Dijkstra monads [Ddwp], [Ddwlp], [Dawp], [Dawlp], [Dasp], [Ddslp]
    and their [_op] variants, with their laws ([Ddwp_laws] &c.). *)

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
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import DijkstraMonads.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.


#[global] Instance OrderedTarget_dwpStExc (S : Type) :
  OrderedTarget (@dwpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_dwlpStExc (S : Type) :
  OrderedTarget (@dwlpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwlpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_awpStExc (S : Type) :
  OrderedTarget (@awpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_awlpStExc (S : Type) :
  OrderedTarget (@awlpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awlpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_aspStExc (S : Type) :
  OrderedTarget (@aspStExc S) (@ordASPStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_aspStExc S) _
    (Eq1Equivalence_ASPStExc S)
    (OrderedMonad_ASPStExc S).

#[global] Instance OrderedTarget_dslpStExc (S : Type) :
  OrderedTarget (@dslpStExc S) (@ordDSLPStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dslpStExc S) _
    (Eq1Equivalence_DSLPStExc S)
    (OrderedMonad_DSLPStExc S).

(** ** The twelve Dijkstra monads with state and exceptions

    Eight WP ones: each of the four readings, at the refinement order and at
    its flip.  Four SP ones: ASP and DSLP, each at its order and at its
    flip.  The same definitions make sense at the base and with state alone,
    with [DM] and [DMop] applied to the morphism of that level. *)
Section Named.
  Context {S A : Type}.

  Definition Ddwp (w : WStExc S A) : Type :=
    DM (@dwpStExc S) (@ordWStExc S) w.
  Definition Ddwp_op (w : WStExc S A) : Type :=
    DMop (@dwpStExc S) (@ordWStExc S) w.
  Definition Ddwlp (w : WStExc S A) : Type :=
    DM (@dwlpStExc S) (@ordWStExc S) w.
  Definition Ddwlp_op (w : WStExc S A) : Type :=
    DMop (@dwlpStExc S) (@ordWStExc S) w.
  Definition Dawp (w : WStExc S A) : Type :=
    DM (@awpStExc S) (@ordWStExc S) w.
  Definition Dawp_op (w : WStExc S A) : Type :=
    DMop (@awpStExc S) (@ordWStExc S) w.
  Definition Dawlp (w : WStExc S A) : Type :=
    DM (@awlpStExc S) (@ordWStExc S) w.
  Definition Dawlp_op (w : WStExc S A) : Type :=
    DMop (@awlpStExc S) (@ordWStExc S) w.

  Definition Dasp (w : ASPStExc S A) : Type :=
    DM (@aspStExc S) (@ordASPStExc S) w.
  Definition Dasp_op (w : ASPStExc S A) : Type :=
    DMop (@aspStExc S) (@ordASPStExc S) w.
  Definition Ddslp (w : DSLPStExc S A) : Type :=
    DM (@dslpStExc S) (@ordDSLPStExc S) w.
  Definition Ddslp_op (w : DSLPStExc S A) : Type :=
    DMop (@dslpStExc S) (@ordDSLPStExc S) w.
End Named.

(** All twelve satisfy the laws: the computation monad is lawful. *)
Section NamedLaws.
  Variable S : Type.
  Local Notation EqM := (Eq1Equivalence__stdivexcndNE S).
  Local Notation LawsM := (MonadLawsE__stdivexcndNE S).

  Theorem Ddwp_laws : DijkstraLaws (@dwpStExc S) (@ordWStExc S).
  Proof. exact (DM_laws (@dwpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Ddwp_op_laws : DijkstraLawsOp (@dwpStExc S) (@ordWStExc S).
  Proof. exact (DMop_laws (@dwpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Ddwlp_laws : DijkstraLaws (@dwlpStExc S) (@ordWStExc S).
  Proof. exact (DM_laws (@dwlpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Ddwlp_op_laws : DijkstraLawsOp (@dwlpStExc S) (@ordWStExc S).
  Proof. exact (DMop_laws (@dwlpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Dawp_laws : DijkstraLaws (@awpStExc S) (@ordWStExc S).
  Proof. exact (DM_laws (@awpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Dawp_op_laws : DijkstraLawsOp (@awpStExc S) (@ordWStExc S).
  Proof. exact (DMop_laws (@awpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Dawlp_laws : DijkstraLaws (@awlpStExc S) (@ordWStExc S).
  Proof. exact (DM_laws (@awlpStExc S) (@ordWStExc S) EqM LawsM). Qed.
  Theorem Dawlp_op_laws : DijkstraLawsOp (@awlpStExc S) (@ordWStExc S).
  Proof. exact (DMop_laws (@awlpStExc S) (@ordWStExc S) EqM LawsM). Qed.

  Theorem Dasp_laws : DijkstraLaws (@aspStExc S) (@ordASPStExc S).
  Proof. exact (DM_laws (@aspStExc S) (@ordASPStExc S) EqM LawsM). Qed.
  Theorem Dasp_op_laws : DijkstraLawsOp (@aspStExc S) (@ordASPStExc S).
  Proof. exact (DMop_laws (@aspStExc S) (@ordASPStExc S) EqM LawsM). Qed.
  Theorem Ddslp_laws : DijkstraLaws (@dslpStExc S) (@ordDSLPStExc S).
  Proof. exact (DM_laws (@dslpStExc S) (@ordDSLPStExc S) EqM LawsM). Qed.
  Theorem Ddslp_op_laws : DijkstraLawsOp (@dslpStExc S) (@ordDSLPStExc S).
  Proof. exact (DMop_laws (@dslpStExc S) (@ordDSLPStExc S) EqM LawsM). Qed.
End NamedLaws.

Lemma wpStExc_typing_pointwise {S A} (σ : forall A, divndNE A -> WPure A)
  (m : stdivexcndNE S A) (w : WStExc S A) :
  ordWStExc (stateT_map S (optionT_map σ) A m) w
  <-> forall s,
        WP_le (σ _ (unOptionT (runStateT m s))) (unOptionT (runStateT w s)).
Proof. reflexivity. Qed.
