(** * Monad laws for the fixed-input predicate monad on [Rel A].

    This file proves [Eq1Equivalence] and [MonadLawsE] for the
    [Monad_Rel] / [Eq1_Rel] instances defined in [Taxonomy/PredMonad.v],
    plus sanity-check instances for the monad-view specification types
    [progPredM] and [nditPredM]. *)

From Coq Require Import
  RelationClasses.
From ExtLib Require Import
  Monad
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy Require Import Rel ProgFacts PredMonad.
From Hammer Require Import Tactics.

(* ================================================================= *)
(** ** [Rel A] monad laws                                            *)
(* ================================================================= *)

#[global]
Instance Eq1Equivalence_Rel {A}
  : @Eq1Equivalence (Rel A) _ Eq1_Rel.
Proof.
  constructor; repeat intro; unfold eq1, Eq1_Rel in *.
  - reflexivity.
  - symmetry. apply H.
  - etransitivity; [apply H | apply H0].
Qed.

#[global]
Instance MonadLawsE_Rel {A} : @MonadLawsE (Rel A) Eq1_Rel _.
Proof.
  constructor.
  - (* bind_ret_l *)
    intros B C f x a c.
    cbn. unfold bindPred, retPred. sauto limit: 200.
  - (* bind_ret_r *)
    intros B x a b.
    cbn. unfold bindPred, retPred. sauto limit: 200.
  - (* bind_bind *)
    intros B C D x f g a d.
    cbn. unfold bindPred. sauto limit: 200.
  - (* Proper_bind *)
    intros B C m1 m2 Hm k1 k2 Hk a c.
    cbn. unfold bindPred.
    unfold eq1, Eq1_Rel in Hm.
    split; intros [b [Hm1 Hk1]]; exists b; split;
      [apply Hm | apply (Hk b a c) | apply Hm | apply (Hk b a c)]; assumption.
Qed.

(* ================================================================= *)
(** ** Monad-view spec type sanity checks                             *)
(* ================================================================= *)

(** Sanity check: confirm [MonadLawsE] resolves through the
    transformer stack down to [MonadLawsE_Rel]. *)
Definition MonadLawsE__progPredM (S : Type)
  : @MonadLawsE (progPredM S) _ _ :=
  MonadLawsE_stateT S (optionT (Rel unit)).

Definition MonadLawsE__nditPredM (S : Type)
  : @MonadLawsE (nditPredM S) _ _ :=
  MonadLawsE_stateT S (optionT (optionT (Rel unit))).
