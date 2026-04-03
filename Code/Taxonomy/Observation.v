(** * Observation functions for [prog].

    Maps [prog S A] (deterministic computation via ITree) to
    specification types.

    SP observation: wraps the relational observation with [mkASP],
    yielding [ASPostArr S A], the predicate transformer arrow.

    WP observations: [observationWP] (total) and [observationWLP]
    (partial, tolerates divergence) map into [ProgWP S A]. *)

From ITree Require Import ITree Eq Props.Infinite.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import Prog WP SPost.

Section Observation.

  Variable S : Type.

  (** The observation: a program [m] relates an initial state to
      an outcome [r : option (A * S)] when the ITree evaluates
      (up to [eutt]) to [ret r]. *)
  Definition obsArrowSP {A} (m : prog S A) : ASPostArr S A :=
    mkASP (fun '(tt, s) r =>
      eutt eq (unOptionT (runStateT m s)) (ret r)).

End Observation.

Arguments obsArrowSP {_} {_}.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

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
