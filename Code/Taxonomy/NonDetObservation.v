(** * Observation functions for [ndprog].

    SP observation: maps [ndprog S A] to [ASPostArr S A] via
    set membership in the outcome set.

    WP observations: [obsDWP] (demonic, all outcomes) and
    [obsAWP] (angelic, some outcome) map into [ProgWP S A]. *)

From Coq Require Import Lia.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg WP SPost.

Import MonadNotation.
Open Scope monad_scope.

Section NonDetObservation.

  Variable S : Type.

  (** Underlying relation: result [r] is a reachable outcome of [m]
      from state [s]. *)
  Definition obsRelASP {A} (m : ndprog S A)
    : SPArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      unOptionT (runStateT m s) r.

  (** Wrapped as a predicate transformer arrow. *)
  Definition obsArrowASP {A} (m : ndprog S A) : ASPostArr S A :=
    mkASP (obsRelASP m).

End NonDetObservation.

Arguments obsRelASP {_} {_}.
Arguments obsArrowASP {_} {_}.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

Section NDObservationWP.

  Variable S : Type.

  (** Demonic WP: ALL outcomes satisfy the postcondition. *)
  Definition obsDWP {A} (m : ndprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post => match runStateT m s with
                          | mkOptionT outcomes =>
                              forall oa, outcomes oa -> post oa
                          end)).

  (** Angelic WP: SOME outcome satisfies the postcondition. *)
  Definition obsAWP {A} (m : ndprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post => match runStateT m s with
                          | mkOptionT outcomes =>
                              exists oa, outcomes oa /\ post oa
                           end)).

  (** No WLP because no divergence.  *)

End NDObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsAWP {_} {_}.

(* ================================================================= *)
(** ** SP examples                                                    *)
(* ================================================================= *)

Example progA : ndprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(** All reachable results from precondition [True] have state >= 42. *)
Theorem progA_all :
  forall s r,
    obsRelASP progA (tt, s) r ->
    match r with
    | Some (_, s') => s' >= 42
    | None => False
    end.
Proof.
  intros s [[[] s']|] H; cbn in H; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  forall s, obsRelASP progA (tt, s) (Some (tt, 42)).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). split; [reflexivity|].
  exists (Some (42, 42)). split; [reflexivity|].
  left. reflexivity.
Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  forall s, obsRelASP progA (tt, s) (Some (tt, 43)).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). split; [reflexivity|].
  exists (Some (42, 42)). split; [reflexivity|].
  right. reflexivity.
Qed.

(* ================================================================= *)
(** ** WP examples                                                    *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

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
