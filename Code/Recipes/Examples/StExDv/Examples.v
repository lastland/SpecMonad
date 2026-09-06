From Coq Require Import PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Recipes.Examples.StExDv Require Import Program.

Import MonadNotation.
Open Scope monad_scope.

Definition orP {S A}
  (m1 m2 : prog S A) : prog S A :=
  nditOr S m1 m2.

Definition spinP {S A} : prog S A :=
  @nditSpin S A.

Definition pickP {S A} : prog S A :=
  mkStateT (fun s =>
    @mkOptionT (optionT SetM) _ (
      @mkOptionT SetM _ (fun oa =>
        exists a : A, oa = Some (Some (a, s))))).

Definition progA : prog nat unit :=
  put 42 ;;
  s <- get ;;
  orP (put s) (put (s + 1)).

Definition progB : prog nat unit :=
  put 42 ;;
  s <- get ;;
  orP (put s) spinP.

Definition progRet : prog nat unit :=
  ret tt.

Definition preEq0 : nat -> Prop :=
  fun s => s = 0.

Definition postEq0 : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, 0).

Definition progEx : prog nat unit :=
  s <- get ;;
  orP (put (s + 1)) (put 42).

Definition P0 : nat -> Prop :=
  fun s => s = 0.

Module OHearnExample.

  Definition example_state : prog (nat * nat * nat) unit :=
    s <- get ;;
    let '(x, y, _) := s in
    if Nat.even x then
      if negb (Nat.even y) then put (x, y, 42) else ret tt
    else ret tt.

End OHearnExample.

Module WithdrawExample.

  Definition progloom : prog nat unit :=
    amount <- pickP ;;
    balance <- get ;;
    if Nat.ltb balance amount then raise tt
    else put (balance - amount).

  Definition progloom_harder : prog nat unit :=
    amount <- pickP ;;
    balance <- get ;;
    if Nat.even balance then raise tt
    else put (balance - amount).

  Definition exceptionPost : option (unit * nat) -> Prop :=
    fun r =>
      match r with
      | Some (tt, _) => False
      | None => True
      end.

End WithdrawExample.
