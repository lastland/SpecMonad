(** * Reaching a bug: from every start state, or from some

    Two withdrawal programs contrast the two readings of "a bug is
    reachable": [progloom_awp_under] (from EVERY start state satisfying the
    precondition, some run raises) against [progloom_asp_under] (the raise
    is reached from SOME such state), and their failure and success on
    [progloom_harder]. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

(** A withdrawal: overdrawing raises. *)
Definition progloom : stdivexcndNE nat unit :=
  amount <- pickStExc ;;
  balance <- get ;;
  if Nat.ltb balance amount then raiseStExc else put (balance - amount).

(** A variant in which the raise depends on the balance and not on the
    amount picked. *)
Definition progloom_harder : stdivexcndNE nat unit :=
  amount <- pickStExc ;;
  balance <- get ;;
  if Nat.even balance then raiseStExc else put (balance - amount).

Lemma progloom_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progloom s o
  <-> exists n, o = if Nat.ltb s n then Some None else Some (Some (tt, s - n)).
Proof.
  unfold progloom. split.
  - intro H. apply (proj1 (outStExc_bind _ _ _ _)) in H. destruct H as [o1 [H1 H2]].
    apply (proj1 (outStExc_pick _ _)) in H1. destruct H1 as [n H1]. subst o1.
    cbn beta iota in H2.
    apply (proj1 (outStExc_bind _ _ _ _)) in H2. destruct H2 as [o2 [H2 H3]].
    apply (proj1 (outStExc_get _ _)) in H2. subst o2. cbn beta iota in H3.
    exists n. destruct (Nat.ltb s n).
    + apply (proj1 (outStExc_raise _ _)) in H3. exact H3.
    + apply (proj1 (outStExc_put _ _ _)) in H3. exact H3.
  - intros [n H]. apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (n, s))).
    split; [ apply (proj2 (outStExc_pick _ _)); exists n; reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (s, s))).
    split; [ apply (proj2 (outStExc_get _ _)); reflexivity |]. cbn beta iota.
    destruct (Nat.ltb s n).
    + apply (proj2 (outStExc_raise _ _)). exact H.
    + apply (proj2 (outStExc_put _ _ _)). exact H.
Qed.

Lemma progloom_harder_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progloom_harder s o
  <-> exists n, o = if Nat.even s then Some None else Some (Some (tt, s - n)).
Proof.
  unfold progloom_harder. split.
  - intro H. apply (proj1 (outStExc_bind _ _ _ _)) in H. destruct H as [o1 [H1 H2]].
    apply (proj1 (outStExc_pick _ _)) in H1. destruct H1 as [n H1]. subst o1.
    cbn beta iota in H2.
    apply (proj1 (outStExc_bind _ _ _ _)) in H2. destruct H2 as [o2 [H2 H3]].
    apply (proj1 (outStExc_get _ _)) in H2. subst o2. cbn beta iota in H3.
    exists n. destruct (Nat.even s).
    + apply (proj1 (outStExc_raise _ _)) in H3. exact H3.
    + apply (proj1 (outStExc_put _ _ _)) in H3. exact H3.
  - intros [n H]. apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (n, s))).
    split; [ apply (proj2 (outStExc_pick _ _)); exists n; reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (s, s))).
    split; [ apply (proj2 (outStExc_get _ _)); reflexivity |]. cbn beta iota.
    destruct (Nat.even s).
    + apply (proj2 (outStExc_raise _ _)). exact H.
    + apply (proj2 (outStExc_put _ _ _)). exact H.
Qed.

(** Angelic total correctness: from EVERY positive balance some run of
    [progloom] raises (withdraw more than the balance). *)
Theorem progloom_awp_under :
  triple (@awpStExc nat) progloom Under
    (fun balance => balance > 0)
    (fun r => r = None).
Proof.
  intros s _. apply (proj2 (awpStExc_read progloom s _)).
  exists (Some None). split; [| reflexivity ].
  apply progloom_out. exists (S s).
  rewrite (proj2 (Nat.ltb_lt s (S s)) (Nat.lt_succ_diag_r s)). reflexivity.
Qed.

(** Incorrectness: the raise is reached from SOME positive balance.  Same
    program, same pre- and postcondition; only the triple differs. *)
Theorem progloom_asp_under :
  triple (@aspStExc nat) progloom Under
    (fun balance => balance > 0)
    (fun r => r = None).
Proof.
  intros r Hr. subst r.
  apply (proj2 (aspStExc_read progloom (fun balance : nat => balance > 0) _)).
  exists 1. split; [ lia |]. apply progloom_out. exists 2. reflexivity.
Qed.

(** In [progloom_harder] the raise happens exactly from an even balance, so
    it is not reached from every positive balance ... *)
Theorem progloom_harder_not_awp_under :
  ~ triple (@awpStExc nat) progloom_harder Under
      (fun balance => balance > 0)
      (fun r => r = None).
Proof.
  intro H. specialize (H 1 (Nat.lt_0_succ 0)).
  pose proof (proj1 (awpStExc_read progloom_harder 1 _) H) as H'.
  clear H. rename H' into H.
  destruct H as [o [Ho Hq]]. apply progloom_harder_out in Ho.
  destruct Ho as [n Ho]. subst o. discriminate Hq.
Qed.

(** ... but it is reached from some. *)
Theorem progloom_harder_asp_under :
  triple (@aspStExc nat) progloom_harder Under
    (fun balance => balance > 0)
    (fun r => r = None).
Proof.
  intros r Hr. subst r.
  apply (proj2 (aspStExc_read progloom_harder
                  (fun balance : nat => balance > 0) _)).
  exists 2. split; [ lia |]. apply progloom_harder_out. exists 0. reflexivity.
Qed.

