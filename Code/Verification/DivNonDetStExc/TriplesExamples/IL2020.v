(** * O'Hearn, "Incorrectness Logic" (POPL 2020), Example 3.1

    An incorrectness triple: every final state with [z = 42], [x] even and
    [y] odd is reached from a start state with [z = 11]. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

(** O'Hearn, "Incorrectness Logic", Example 3.1: set [z] to [42] when [x] is
    even and [y] is odd; otherwise leave the state alone. *)
Definition example_state : stdivexcndNE (nat * nat * nat) unit :=
  s <- get ;;
  let '(x, y, _) := s in
  if Nat.even x then
    if negb (Nat.even y) then put (x, y, 42) else ret tt
  else ret tt.

Lemma example_state_out (x y z : nat) (o : option (option (unit * (nat * nat * nat)))) :
  outStExc example_state (x, y, z) o
  <-> o = Some (Some (tt, if Nat.even x
                          then if negb (Nat.even y) then (x, y, 42) else (x, y, z)
                          else (x, y, z))).
Proof.
  unfold example_state. split.
  - intro H. apply (proj1 (outStExc_bind _ _ _ _)) in H. destruct H as [o1 [H1 H2]].
    apply (proj1 (outStExc_get _ _)) in H1. subst o1. cbn beta iota in H2.
    destruct (Nat.even x); [ destruct (negb (Nat.even y)) |].
    + apply (proj1 (outStExc_put _ _ _)) in H2. exact H2.
    + apply (proj1 (outStExc_ret _ _ _)) in H2. exact H2.
    + apply (proj1 (outStExc_ret _ _ _)) in H2. exact H2.
  - intro H. apply (proj2 (outStExc_bind _ _ _ _)).
    exists (Some (Some ((x, y, z), (x, y, z)))).
    split; [ apply (proj2 (outStExc_get _ _)); reflexivity |]. cbn beta iota.
    destruct (Nat.even x); [ destruct (negb (Nat.even y)) |].
    + apply (proj2 (outStExc_put _ _ _)). exact H.
    + apply (proj2 (outStExc_ret _ _ _)). exact H.
    + apply (proj2 (outStExc_ret _ _ _)). exact H.
Qed.

(** O'Hearn's Example 3.1: every final state with [z = 42], [x] even and [y]
    odd is reached from a state with [z = 11]. *)
Theorem example_incorrect :
  triple (@aspStExc (nat * nat * nat)) example_state Under
    (fun '(_, _, z) => z = 11)
    (fun r =>
       match r with
       | Some (_, (x, y, z)) =>
           z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
       | None => False
       end).
Proof.
  intros [[[] [[x y] z]]|] H; [| contradiction ].
  destruct H as [Hz [Hx Hy]]. subst z.
  apply (proj2 (aspStExc_read example_state (fun '(_, _, z) => z = 11) _)).
  exists (x, y, 11). split; [ reflexivity |].
  apply example_state_out. rewrite Hx, Hy. reflexivity.
Qed.
