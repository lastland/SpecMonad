(** * [WPred]/[ProgWPred] laws, bridged to [SetM]/[ndprog].

    [WPred] is a transparent alias for [SetM := A -> Prop] (see
    [WPred.v]).  Its [Eq1] and [MonadLawsE] instances are bridged to
    [SetM]'s (proved in [NonDetProgFacts]); no law is reproved here.

    [ProgWPred S = stateT S (optionT WPred)] then inherits [MonadLawsE]
    via the generic [optionT] and [stateT] instances from [ProgFacts].
    Unfolded, [ProgWPred S A = S -> option (A * S) -> Prop]. *)

From Coq Require Import
  Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness Require Import
  Taxonomy.WPred
  Taxonomy.NonDetProg
  Taxonomy.NonDetProgFacts
  Taxonomy.ProgFacts.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [WPred], bridged to [SetM]          *)
(* ================================================================= *)

#[global]
Instance Eq1_WPred : Eq1 WPred := Eq1_SetM.

#[global]
Instance Eq1Equivalence_WPred
  : @Eq1Equivalence WPred Monad_WPred Eq1_WPred :=
  @Eq1Equivalence_SetM.

#[global]
Instance MonadLawsE_WPred
  : @MonadLawsE WPred Eq1_WPred Monad_WPred :=
  @MonadLawsE_SetM.

(* ================================================================= *)
(** ** [MonadLawsE] for [ProgWPred S]                                *)
(* ================================================================= *)

Section ProgWPredFacts.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_WPred]   (Leibniz eq)
      → [Eq1_optionT]   (eq on unwrapped WPred)
      → [Eq1_stateT]    (pointwise eq)

      and similarly for [MonadLawsE]. *)

  Definition Eq1__ProgWPred : Eq1 (ProgWPred S) :=
    Eq1_stateT S (optionT WPred).

  Definition MonadLawsE__ProgWPred
    : @MonadLawsE (ProgWPred S) _ (Monad__ProgWPred S) :=
    MonadLawsE_stateT S (optionT WPred).

End ProgWPredFacts.
