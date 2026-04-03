From Coq Require Import
  Lia Program.Tactics.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Props.Infinite.
From Hammer Require Import Tactics.

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

(** * Import excluded middle. *)
Require Import Coq.Logic.Classical_Prop.

Section NDObservationSP.

  Variable S : Type.

  (** Angelic SP: result [r] is reachable from [pre]. *)
  (** I'm not sure if this is correct.  *)
  #[program]
    Definition obsASP {A} (m : ndprog S A) : ProgSPost S A :=
    mkStateT
      (fun s => @mkOptionT PureSPost _
                 (fun pre r => match runStateT m s with
                          | mkOptionT outcomes =>
                              outcomes r /\ pre
                          end)).
  Next Obligation.
    destruct (runStateT m s); exact (proj2 H).
  Qed.
  Next Obligation.
    destruct (runStateT m s) in *; split;
      [exact (proj1 H0) | exact (H (proj2 H0))].
  Qed.

  (** Demonic SLP. *)
  (** * TODO: I do not know how to write this one.

  According to "A Taxonomy of Hoare-Like Logics", this should include (1)
  exclusively from (initial) states in Σ or (2) entirely unreachable (i.e. from
  any initial state in Σ) by the computation of the program.

  This is using the fact that DSLP is the contrapositive of ASP. However, we can
  no longer show that the postcondition implies pre, a key for showing that
  SPost satisfies monad laws.  *)
  #[program]
    Definition obsDSLP {A} (m : ndprog S A) : ProgSPost S A :=
    mkStateT
      (fun s => @mkOptionT PureSPost _
                 (fun pre r => not (unOptionT (runStateT (obsASP m) s) (not pre) r))).
  Next Obligation.
    destruct (runStateT m s).
    assert (Hc: pre \/ ~ pre) by apply classic.
    destruct Hc; [assumption |].
    exfalso. apply H. split; [| tauto]. (* Stuck *)
  Admitted.
  Next Obligation.
  Admitted.
  
End NDObservationSP.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.

Example progA_ASP := obsASP progA.

Theorem progA_ASP_all :
  forall s r,
    proj1_sig
      (proj1_sig (unOptionT (runStateT progA_ASP s)) True) r ->
    (exists n, r = Some (tt, n) /\ n >= 42).
Proof.
  intros. cbn in H. destruct H as [[a [? Hsp]] _].
  subst. cbn in Hsp. destruct Hsp as [a [? Hsp]]. subst.
  cbn in Hsp. destruct Hsp; subst;
    eapply ex_intro; (split; [reflexivity | lia]).
Qed.
