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

  (** No WLP because no divergence. In this case, they are not even definable.
  *)

End NDObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsAWP {_} {_}.

(* ================================================================= *)
(** ** SP observations                                                *)
(* ================================================================= *)


Section NDObservationSP.

  Variable S : Type.

  Definition obsASP {A} (m : ndprog S A) : ASPostArr S A :=
    mkASP (fun '(_, s0) r => unOptionT (runStateT m s0) r).

  Definition obsDSLP {A} (m : ndprog S A) : DSLPostArr S A :=
    mkDSLP (fun '(_, s0) r => unOptionT (runStateT m s0) r). 

  #[program] Definition obsASLP {A} (m : ndprog S A) :
    (unit * S -> Prop) -> (option (A * S) -> Prop) :=
    fun pre r => sp_pt (obsASP m) pre r \/ sp_pt (obsDSLP m) pre r. 

  #[program] Definition obsDSP {A} (m : ndprog S A) :
    (unit * S -> Prop) -> (option (A * S) -> Prop) :=
    fun pre r => sp_pt (obsASP m) pre r /\ sp_pt (obsDSLP m) pre r.
  
End NDObservationSP.

Arguments obsASP {_} {_}.
Arguments obsASLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsDSLP {_} {_}.


Example progA : ndprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

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

(* ================================================================= *)
(** ** SP examples                                                    *)
(* ================================================================= *)

(** All reachable results from precondition [True] have state >= 42. *)
#[program] Theorem progA_all :
  forall (s : nat) r,
    sp_pt (obsASP progA) (fun _ => True) r ->
    match r with
    | Some (_, s') => s' >= 42
    | None => False
    end.
Proof.
  intros s [[[] s']|] H; cbn in H; sauto.
Qed.

(** State 42 is reachable. *)
#[program] Theorem progA_42 :
  sp_pt (obsASP progA) (fun _ => True) (Some (tt, 42)).
Proof.
  intros. cbn. unfold asp.
  exists (tt, 42). split; [reflexivity|].
  eapply ex_intro. split; [reflexivity|]. cbn.
  eapply ex_intro. split; [reflexivity|]. cbn.
  left. reflexivity.
Qed.

(** State 43 is also reachable. *)
#[program] Theorem progA_43 :
  sp_pt (obsASP progA) (fun _ => True) (Some (tt, 43)).
Proof.
  intros. cbn. unfold asp.
  exists (tt, 42). split; [reflexivity|].
  eapply ex_intro. split; [reflexivity|]. cbn.
  eapply ex_intro. split; [reflexivity|]. cbn.
  right. reflexivity.
Qed.

