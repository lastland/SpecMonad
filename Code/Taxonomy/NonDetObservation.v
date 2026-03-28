From Coq Require Import Program.Tactics.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.

From Incorrectness.Taxonomy Require Import
  NonDetProg WP SPost.

Section NDObservationWP.

  Variable S : Type.

  (** Demonic WP (over-approximation): ALL outcomes satisfy the
      postcondition. *)
  Definition demonicWP {A} (m : ndprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post => match runStateT m s with
                          | mkOptionT outcomes =>
                              forall oa, outcomes oa -> post oa
                          end)).

  (** Angelic WP (under-approximation): SOME outcome satisfies the
      postcondition. *)
  Definition angelicWP {A} (m : ndprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post => match runStateT m s with
                          | mkOptionT outcomes =>
                              exists oa, outcomes oa /\ post oa
                          end)).

End NDObservationWP.

Section NDObservationSP.

  Variable S : Type.

  (** Angelic SP (forward under-approximation): result [r] is
      reachable from [pre]. *)
  #[program]
    Definition angelicSP {A} (m : ndprog S A) : ProgSPost S A :=
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
