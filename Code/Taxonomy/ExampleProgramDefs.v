(** * Example programs

    The example [nditprog] programs exercised by the observation files and by
    [ExamplePrograms.v].

    They live in their own file because they are used from BOTH directions:
    [SPNonDetItObservations.v] and [OldSP/OldSPObservations.v] state example
    lemmas about them, while [ExamplePrograms.v] proves triples about them
    using the observations those files define.  Keeping the definitions here
    breaks what would otherwise be an import cycle. *)

From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg ProgFacts WP Pred PredFacts SPost WPred.

Import MonadNotation.
Open Scope monad_scope.

Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

Example progB : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (spinP _).

Example progRet : nditprog nat unit := ret tt.

Example progEx : nditprog nat unit :=
  s <- get ;;
  orP _ (put (s + 1)) (put 42).

(** O'Hearn, "Incorrectness Logic", Example 3.1: swap [z] with [42] when [x]
    is even and [y] is odd; otherwise leave the state alone. *)
Definition example_state : nditprog (nat * nat * nat) unit :=
    s <- get ;;
    let '(x, y, _) := s in
    if Nat.even x then
      if negb (Nat.even y) then put (x, y, 42) else ret tt
    else ret tt.
(** Pre/postcondition used by the [progRet] examples in both the old and the
    new presentation. *)
Definition preEq0 : nat -> Prop := fun s => s = 0.
Definition postEq0 : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, 0).

