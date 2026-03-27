From Coq Require Import List.
From ITree Require Import ITree Eq Props.Infinite.
From ExtLib Require Import
  Monad MonadTrans MonadState MonadExc
  StateMonad OptionMonad List.          
From Hammer Require Import Tactics.

From Incorrectness.Taxonomy Require Import Prog Spec.

Section ObservationWP.

  Variable S : Type.
  
  Definition observationWP {A} (m : prog S A) : ProgSpec S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                        | mkOptionT o => exists r, post r /\ eutt eq o (ret r)
                        end)).

  Definition observationWLP {A} (m : prog S A) : ProgSpec S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (exists r, post r /\ eutt eq o (ret r)) \/
                                           any_infinite o
                        end)).
  
End ObservationWP.

