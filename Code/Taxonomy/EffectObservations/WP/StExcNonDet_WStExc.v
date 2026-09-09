(** * Observation functions for [stexcnd].

    SP observation: maps [stexcnd S A] to [ASPostArr S A] via
    set membership in the outcome set.

    WP observations: [obsDWP] (demonic, all outcomes) and
    [obsAWP] (angelic, some outcome) map into [WStExc S A]. *)

From Coq Require Import Lia.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

Section NDObservationWP.

  Variable S : Type.

  (** Demonic WP: ALL outcomes satisfy the postcondition. *)
  Lemma obsDWP_mono {A} (m : stexcnd S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT outcomes => forall oa, outcomes oa -> post oa
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [outcomes].
    intros oa Ho. exact (Hpq oa (H oa Ho)).
  Qed.

  Definition obsDWP {A} (m : stexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsDWP_mono m s))).

  (** Angelic WP: SOME outcome satisfies the postcondition. *)
  Lemma obsAWP_mono {A} (m : stexcnd S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT outcomes => exists oa, outcomes oa /\ post oa
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [outcomes].
    destruct H as [oa [Ho Hp]]. exists oa. split; [ exact Ho | exact (Hpq oa Hp) ].
  Qed.

  Definition obsAWP {A} (m : stexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsAWP_mono m s))).

  (** No WLP because no divergence. In this case, they are not even definable.
  *)

End NDObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsAWP {_} {_}.

(* ================================================================= *)
(** ** WP examples                                                    *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA_stexcnd.
Example progA_AWP := obsAWP progA_stexcnd.

Theorem progA_DWP_all :
  forall s, unOptionT (runStateT progA_DWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s >= 42
            | None => False
            end).
Proof.
  intros. cbn. intros []; sauto.
Qed.

Theorem progA_DWP_not42 :
  not (forall s, unOptionT (runStateT progA_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 (Some (tt, 43))).
  cbn in contra.
  assert (H: 43 = 42 -> False) by lia. apply H.
  apply contra. exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. right. reflexivity.
Qed.

Theorem progA_DWP_not43 :
  not (forall s, unOptionT (runStateT progA_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 43
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 (Some (tt, 42))).
  cbn in contra.
  assert (H: 42 = 43 -> False) by lia. apply H.
  apply contra. exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. left. reflexivity.
Qed.

Theorem progA_AWP_all :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s >= 42
            | None => False
            end).
Proof.
  intros. cbn. exists (Some (tt, 42)). split; [| lia].
  exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. left. reflexivity.
Qed.

Theorem progA_AWP_42 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn. exists (Some (tt, 42)). split; [| lia].
  exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. left. reflexivity.
Qed.

Theorem progA_AWP_43 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 43
            | None => False
            end).
Proof.
  intros. cbn. exists (Some (tt, 43)). split; [| lia].
  exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. right. reflexivity.
Qed.
