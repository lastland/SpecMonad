From Coq Require Import
  Lia Program.Tactics.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.

From Incorrectness.Taxonomy Require Import
  NonDetItProg WP SPost.

Section NDItObservationWP.

  Variable S : Type.

  (** Demonic WP (total): ALL outcomes must terminate and satisfy
      the postcondition.  Divergence is not acceptable. *)
  Definition obsDWP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            forall oa, outcomes oa ->
                              match oa with
                              | Some r => post r
                              | None => False
                              end
                        end
                    end)).

  (** Demonic WLP (partial): ALL terminating outcomes satisfy the
      postcondition.  Divergence is acceptable. *)
  Definition obsDWLP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            forall oa, outcomes oa ->
                              match oa with
                              | Some r => post r
                              | None => True
                              end
                        end
                    end)).

  (** Angelic WP (total): SOME terminating outcome satisfies the
      postcondition. *)
  Definition obsAWP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            exists r, outcomes (Some r) /\ post r
                        end
                    end)).

  (** Angelic WLP (partial): SOME terminating outcome satisfies the
      postcondition, OR divergence is possible. *)
  Definition obsAWLP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            (exists r, outcomes (Some r) /\ post r) \/
                            outcomes None
                        end
                    end)).

End NDItObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Examples: pure nondeterminism (no divergence)                  *)
(* ================================================================= *)

Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  forall s, unOptionT (runStateT progA_DWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s >= 42
            | None => False
            end).
Proof.
  intros. cbn. intros [[[]|]|] H; sauto.
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 :
  not (forall s, unOptionT (runStateT progA_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 (Some (Some (tt, 43)))).
  sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). sauto.
Qed.

Theorem progA_AWP_43 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 43
            | None => False
            end).
Proof.
  intros. cbn.
  exists (Some (tt, 43)). sauto.
Qed.

(* ================================================================= *)
(** ** Examples: nondeterminism + divergence                          *)
(* ================================================================= *)

Example progB : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (spinP _).

Example progB_DWP := obsDWP progB.
Example progB_DWLP := obsDWLP progB.
Example progB_AWP := obsAWP progB.

(** DWP is unprovable: the divergent branch forces [False]. *)
Theorem progB_DWP_unprovable :
  not (forall s, unOptionT (runStateT progB_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored. *)
Theorem progB_DWLP_42 :
  forall s, unOptionT (runStateT progB_DWLP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn. intros [[[]|]|] H; try exact I; sauto.
Qed.

(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  forall s, unOptionT (runStateT progB_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). sauto.
Qed.

(* ================================================================= *)
(** ** Angelic SP                                                     *)
(* ================================================================= *)

Require Import Coq.Logic.Classical_Prop.

Section NDItObservationSP.

  Variable S : Type.

  (** Angelic SP: result [r] is reachable from [pre]. *)
  #[program]
    Definition obsASP {A} (m : nditprog S A) : ProgSPost S A :=
    mkStateT
      (fun s => @mkOptionT PureSPost _
                 (fun pre => exist _
                    (fun r =>
                       match runStateT m s with
                       | mkOptionT inner =>
                           match inner with
                           | mkOptionT outcomes =>
                               outcomes (Some r) /\ pre
                           end
                       end) _)).
  Next Obligation.
    destruct (runStateT m s) as [[outcomes]]; exact (proj2 H).
  Qed.
  Next Obligation.
    destruct (runStateT m s) as [[outcomes]] eqn:? in *;
      split; [exact (proj1 H0) | exact (H (proj2 H0))].
  Qed.

  (** Demonic SLP: contrapositive of ASP. *)
  #[program]
    Definition obsDSLP {A} (m : nditprog S A) : ProgSPost S A :=
    mkStateT
      (fun s => @mkOptionT PureSPost _
                 (fun pre => exist _
                    (fun r => not (unOptionT (runStateT (obsASP m) s) (not pre) r)) _)).
  Next Obligation.
    destruct (runStateT m s) as [[outcomes]].
    assert (Hc: pre \/ ~ pre) by apply classic.
    destruct Hc; [assumption |].
    exfalso. apply H. split; [| tauto].
  Admitted.
  Next Obligation.
  Admitted.

End NDItObservationSP.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.

Example progA_ASP := obsASP progA.

Theorem progA_ASP_all :
  forall s r,
    proj1_sig
      (proj1_sig (unOptionT (runStateT progA_ASP s)) True) r ->
    (exists n, r = Some (tt, n) /\ n >= 42).
Proof.
  intros. cbn in H. sauto.
Qed.
