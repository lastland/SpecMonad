From Coq Require Import Lia Program.Tactics.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Props.Infinite.
From Hammer Require Import Hammer Tactics.

From Incorrectness.Taxonomy Require Import
  NonDetProg WP SPost.

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

Import MonadNotation.
Open Scope monad_scope.

(** * Some examples using DWP and AWP. *)

Example progA : ndprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

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

Theorem progA_DWP_one :
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

Theorem progA_DWP_two :
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

Theorem progA_AWP_one :
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

Theorem progA_AWP_two :
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

Section NDObservationSP.

  Variable S : Type.

  (** * TODO: Questionable *)
  (** Angelic SP: result [r] is reachable from [pre]. *)
  #[program]
    Definition obsASP {A} (m : ndprog S A) : ProgSPost S A :=
    mkStateT
      (fun s => @mkOptionT PureSPost _
                 (fun pre => exist _
                    (fun r => match runStateT m s with
                          | mkOptionT outcomes =>
                              outcomes r /\ pre
                          end) _)).
  Next Obligation.
    destruct (runStateT m s); exact (proj2 H).
  Qed.
  Next Obligation.
    destruct (runStateT m s) in *; split;
      [exact (proj1 H0) | exact (H (proj2 H0))].
  Qed.

  (** * TODO: Questionable; right now the same as above *)
  (** Demonic SLP. *)
  #[program]
    Definition obsDSLP {A} (m : ndprog S A) : ProgSPost S A :=
    mkStateT
      (fun s => @mkOptionT PureSPost _
                 (fun pre => exist _
                    (fun r => match runStateT m s with
                          | mkOptionT outcomes =>
                              outcomes r /\ pre
                          end) _)).
  Next Obligation.
    destruct (runStateT m s); exact (proj2 H).
  Qed.
  Next Obligation.
    destruct (runStateT m s) in *; split;
      [exact (proj1 H0) | exact (H (proj2 H0))].
  Qed.
  
End NDObservationSP.
