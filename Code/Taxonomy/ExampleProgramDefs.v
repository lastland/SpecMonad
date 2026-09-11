(** * Example programs

    The example programs exercised by the observation files, by
    [Taxonomy_StDivExcNonDet_StExc.v], and by [OldSP/OldSPObservations.v].

    They live in their own file because every one of those files states
    lemmas or triples about them using the observations it defines, so the
    definitions cannot sit in any single one of them without creating an
    import cycle.  Most are [stdivexcnd] programs; [progA_stexcnd] and
    [progA_stdivitree] are the same shapes read in the other computation
    monads. *)

From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr RelSPPairArr.

Import MonadNotation.
Open Scope monad_scope.

Example progA : stdivexcnd nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

Example progB : stdivexcnd nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (spinP _).

Example progRet : stdivexcnd nat unit := ret tt.

Example progEx : stdivexcnd nat unit :=
  s <- get ;;
  orP _ (put (s + 1)) (put 42).

(** O'Hearn, "Incorrectness Logic", Example 3.1: swap [z] with [42] when [x]
    is even and [y] is odd; otherwise leave the state alone. *)
Definition example_state : stdivexcnd (nat * nat * nat) unit :=
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


(** [progA] transposed to the divergence-free monad: the same program, read in
    [stexcnd].  Exercised by [WP/StExcNonDet_WStExc.v]. *)
Example progA_stexcnd : stexcnd nat unit :=
  put 42 ;;
  s <- get ;;
  StExcNonDet.orP _ (put s) (put (s + 1)).

(** The deterministic variant, in the ITree monad.  Exercised by
    [WP/StDivITree_WStExc.v]. *)
Example progA_stdivitree : stdivitree nat unit :=
  put 42 ;;
  s <- get ;;
  put s.

(** O'Hearn's withdrawal example: overdrawing raises.  The angelic scheduler
    can always force the [raise] by picking an amount above the balance. *)
Definition progloom : stdivexcnd nat unit :=
  amount  <- pickP ;;
  balance <- get ;;
  if Nat.ltb balance amount then raise tt else put (balance - amount).

(** A variant where the [raise] depends on the state rather than on the
    picked amount, so angelic coverage fails from an odd balance. *)
Definition progloom_harder : stdivexcnd nat unit :=
  amount  <- pickP ;;
  balance <- get ;;
  if Nat.even balance then raise tt else put (balance - amount).
