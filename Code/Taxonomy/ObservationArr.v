(** * Arrow-based SP observation for [prog].

    Maps [prog S A] (deterministic computation via ITree) to
    [ASPostArr S A], the predicate transformer arrow.

    The observation wraps the relational observation with [mkASP],
    yielding a bundled predicate transformer. *)

From ITree Require Import ITree Eq.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import Prog SPostArr.

Section ObservationArr.

  Variable S : Type.

  (** The observation: a program [m] relates an initial state to
      an outcome [r : option (A * S)] when the ITree evaluates
      (up to [eutt]) to [ret r]. *)
  Definition obsArrowSP {A} (m : prog S A) : ASPostArr S A :=
    mkASP (fun '(tt, s) r =>
      eutt eq (unOptionT (runStateT m s)) (ret r)).

End ObservationArr.

Arguments obsArrowSP {_} {_}.
