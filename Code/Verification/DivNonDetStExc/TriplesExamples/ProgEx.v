(** * [progEx]: add [1] to the state, or put [42]

    One triple: DSLP [Under]. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.
From Incorrectness.Verification.DivNonDetStExc.TriplesExamples Require Import Common.

Import MonadNotation.
Open Scope monad_scope.

Definition progEx : stdivexcndNE nat unit :=
  s <- get ;;
  orStExc (put (s + 1)) (put 42).

Lemma progEx_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progEx s o
  <-> o = Some (Some (tt, s + 1)) \/ o = Some (Some (tt, 42)).
Proof.
  unfold progEx. split.
  - intro H. apply (proj1 (outStExc_bind _ _ _ _)) in H. destruct H as [o1 [H1 H2]].
    apply (proj1 (outStExc_get _ _)) in H1. subst o1. cbn beta iota in H2.
    apply (proj1 (outStExc_or _ _ _ _)) in H2.
    destruct H2 as [H2|H2]; apply (proj1 (outStExc_put _ _ _)) in H2; [ left | right ];
      exact H2.
  - intro H. apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (s, s))).
    split; [ apply (proj2 (outStExc_get _ _)); reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_or _ _ _ _)).
    destruct H as [H|H]; [ left | right ]; apply (proj2 (outStExc_put _ _ _)); exact H.
Qed.

(** The state [1] is reached by [progEx] only from [0]. *)
Theorem progEx_dslp_under :
  triple (@dslpStExc nat) progEx Under preEq0 (fun r => r = Some (tt, 1)).
Proof.
  intros r Hr. subst r. apply (proj2 (dslpStExc_read progEx preEq0 _)).
  intros s Ho. apply progEx_out in Ho. unfold preEq0.
  destruct Ho as [Ho|Ho]; injection Ho as Hs; lia.
Qed.

