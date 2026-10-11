(** * The Dijkstra monads of the base morphisms

    The [OrderedTarget] instances of the WP, ASP and DSLP base morphisms:
    each names the natural order of its target, which is all the
    construction of [Generic/DijkstraMonad.v] needs.  DSP and ASLP have none
    with state; see [SP/DSPMonad.v]. *)

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


(* ================================================================= *)
(** * The liftable morphisms                                          *)
(* ================================================================= *)

(** Each target is ordered, by its natural order, for the monad and the
    equality its morphism is stated with.  The WP targets carry the
    refinement order [WP_le] and its lifts; ASP and DSLP the pointwise order
    of their transformers.

    The DSP and ASLP morphisms have no instance.  DSP and ASLP are not
    specification monads for their natural order: [bind] is not monotone in
    its first argument ([not_OrderedMonad_DSPSt], [not_OrderedMonad_ASLPSt]).
    So they have no Dijkstra monad here. *)

#[global] Instance OrderedTarget_dwpPure :
  OrderedTarget (@dwpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_dwpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_dwlpPure :
  OrderedTarget (@dwlpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_dwlpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_awpPure :
  OrderedTarget (@awpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_awpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_awlpPure :
  OrderedTarget (@awlpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_awlpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_aspPure :
  OrderedTarget (@aspPure) (@ordASP) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_aspPure _
    Eq1Equivalence_ASP
    OrderedMonad_ASP.

#[global] Instance OrderedTarget_dslpPure :
  OrderedTarget (@dslpPure) (@ordDSLP) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_dslpPure _
    Eq1Equivalence_DSLP
    OrderedMonad_DSLP.
