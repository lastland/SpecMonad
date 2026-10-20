(** * Both orders on the SP flavours

    [WPFlavours.v] gives each WP monad its refinement order and the
    converse.  This file does the same for the SP monads of [ASPMonad.v],
    [DSLPMonad.v], [DSPMonad.v] and [ASLPMonad.v], at the pure and the
    state level.

    [OrderedMonad] does not see the direction of an order
    ([OrderedMonad_flip]), so a monad ordered one way is ordered the other:

      [ASP], [DSLP]    pointwise implication and its converse
      [DSP], [ASLP]    inclusion of the denoted relation and its converse

    For the same reason the reading's own order on [DSPSt] and [ASLPSt],
    pointwise implication, fails in both directions
    ([not_OrderedMonad_DSPSt_op], [not_OrderedMonad_ASLPSt_op]). *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.

(* ================================================================= *)
(** ** ASP and DSLP                                                  *)
(* ================================================================= *)

Definition ordASPop {A} : relation (ASP A) := fun m n => ordASP n m.
Definition ordASPStOp {S A} : relation (ASPSt S A) := fun m n => ordASPSt n m.

#[global] Instance OrderedMonad_ASP_op : OrderedMonad ASP (@ordASPop) :=
  OrderedMonad_flip (@ordASP) OrderedMonad_ASP.
#[global] Instance OrderedMonad_ASPSt_op S : OrderedMonad (ASPSt S) (@ordASPStOp S) :=
  OrderedMonad_flip (@ordASPSt S) (OrderedMonad_ASPSt S).

Definition ordDSLPop {A} : relation (DSLP A) := fun m n => ordDSLP n m.
Definition ordDSLPStOp {S A} : relation (DSLPSt S A) := fun m n => ordDSLPSt n m.

#[global] Instance OrderedMonad_DSLP_op : OrderedMonad DSLP (@ordDSLPop) :=
  OrderedMonad_flip (@ordDSLP) OrderedMonad_DSLP.
#[global] Instance OrderedMonad_DSLPSt_op S : OrderedMonad (DSLPSt S) (@ordDSLPStOp S) :=
  OrderedMonad_flip (@ordDSLPSt S) (OrderedMonad_DSLPSt S).

(* ================================================================= *)
(** ** DSP and ASLP                                                  *)
(* ================================================================= *)

Definition Eq1Equivalence_DSPSt S
  : @Eq1Equivalence (DSPSt S) (Monad_DSPSt S) (Eq1_DSPSt S) :=
  @Eq1Equivalence_Arrow (DSPStArr S) _ (ArrowApply_DSPStArr S) (ArrowEq_DSPStArr S).

Definition Eq1Equivalence_ASLPSt S
  : @Eq1Equivalence (ASLPSt S) (Monad_ASLPSt S) (Eq1_ASLPSt S) :=
  @Eq1Equivalence_Arrow (ASLPStArr S) _ (ArrowApply_ASLPStArr S) (ArrowEq_ASLPStArr S).

Definition ordDSPRelOp {A} : relation (DSP A) := fun m n => ordDSPRel n m.
Definition ordDSPStRelOp {S A} : relation (DSPSt S A) := fun m n => ordDSPStRel n m.

#[global] Instance OrderedMonad_DSP_op : OrderedMonad DSP (@ordDSPRelOp) :=
  @OrderedMonad_flip DSP _ _ Eq1Equivalence_DSP (@ordDSPRel) OrderedMonad_DSP.
#[global] Instance OrderedMonad_DSPSt_op S : OrderedMonad (DSPSt S) (@ordDSPStRelOp S) :=
  @OrderedMonad_flip (DSPSt S) _ _ (Eq1Equivalence_DSPSt S) (@ordDSPStRel S)
    (OrderedMonad_DSPSt S).

Definition ordASLPRelOp {A} : relation (ASLP A) := fun m n => ordASLPRel n m.
Definition ordASLPStRelOp {S A} : relation (ASLPSt S A) := fun m n => ordASLPStRel n m.

#[global] Instance OrderedMonad_ASLP_op : OrderedMonad ASLP (@ordASLPRelOp) :=
  @OrderedMonad_flip ASLP _ _ Eq1Equivalence_ASLP (@ordASLPRel) OrderedMonad_ASLP.
#[global] Instance OrderedMonad_ASLPSt_op S : OrderedMonad (ASLPSt S) (@ordASLPStRelOp S) :=
  @OrderedMonad_flip (ASLPSt S) _ _ (Eq1Equivalence_ASLPSt S) (@ordASLPStRel S)
    (OrderedMonad_ASLPSt S).

(** The reading's own order is not a specification-monad order in either
    direction. *)

Theorem not_OrderedMonad_DSPSt_op :
  ~ @OrderedMonad (DSPSt bool) (Monad_DSPSt bool) (Eq1_DSPSt bool)
      (fun A m n => @ordDSPSt bool A n m).
Proof.
  intro H. apply not_OrderedMonad_DSPSt.
  exact (@OrderedMonad_flip (DSPSt bool) _ _ (Eq1Equivalence_DSPSt bool) _ H).
Qed.

Theorem not_OrderedMonad_ASLPSt_op :
  ~ @OrderedMonad (ASLPSt bool) (Monad_ASLPSt bool) (Eq1_ASLPSt bool)
      (fun A m n => @ordASLPSt bool A n m).
Proof.
  intro H. apply not_OrderedMonad_ASLPSt.
  exact (@OrderedMonad_flip (ASLPSt bool) _ _ (Eq1Equivalence_ASLPSt bool) _ H).
Qed.
