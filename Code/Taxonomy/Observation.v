From Coq Require Import Program.Tactics.
From ITree Require Import ITree Eq Props.Infinite.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.

From Incorrectness.Taxonomy Require Import
  Prog WP SPost.

Section ObservationWP.

  Variable S : Type.

  Definition observationWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                        | mkOptionT o => exists r, post r /\ eutt eq o (ret r)
                        end)).

  Definition observationWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (exists r, post r /\ eutt eq o (ret r)) \/
                                           any_infinite o
                        end)).

End ObservationWP.

Section ObservationSP.

  Variable S : Type.

  #[program]
    Definition observationSP {A} (m : prog S A) : ProgSPost S A :=
    mkStateT
      (fun s => mkOptionT
               (fun pre r => eutt eq (unOptionT (runStateT m s)) (ret r) /\ pre)).

  (** What should [slp] be like? *)
End ObservationSP.
