From Coq Require Import List.
From ITree Require Import ITree Eq Props.Infinite.
From ExtLib Require Import
  Monad MonadTrans MonadState MonadExc
  StateMonad OptionMonad List.          
From Hammer Require Import Tactics.

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
               (fun pre => match runStateT m s with
                        | mkOptionT o => fun r => eutt eq o (ret r) /\ pre
                        end)).

  (** What should [slp] be like? *)
End ObservationSP.
