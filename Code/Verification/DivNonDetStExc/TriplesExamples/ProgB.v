(** * [progB]: put [42], then keep it or diverge

    Every run that terminates ends in state [42], and some run diverges.
    Two triples: DWLP and AWLP [Under]. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

Definition progB : stdivexcndNE nat unit :=
  put 42 ;;
  s <- get ;;
  orStExc (put s) divergeStExc.

Lemma progB_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progB s o <-> o = Some (Some (tt, 42)) \/ o = None.
Proof.
  unfold progB. split.
  - intro H. apply (proj1 (outStExc_bind _ _ _ _)) in H. destruct H as [o1 [H1 H2]].
    apply (proj1 (outStExc_put _ _ _)) in H1. subst o1. cbn beta iota in H2.
    apply (proj1 (outStExc_bind _ _ _ _)) in H2. destruct H2 as [o2 [H2 H3]].
    apply (proj1 (outStExc_get _ _)) in H2. subst o2. cbn beta iota in H3.
    apply (proj1 (outStExc_or _ _ _ _)) in H3. destruct H3 as [H3|H3].
    + apply (proj1 (outStExc_put _ _ _)) in H3. left. exact H3.
    + apply (proj1 (outStExc_diverge _ _)) in H3. right. exact H3.
  - intro H. apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (tt, 42))).
    split; [ apply (proj2 (outStExc_put _ _ _)); reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (42, 42))).
    split; [ apply (proj2 (outStExc_get _ _)); reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_or _ _ _ _)). destruct H as [H|H]; subst o.
    + left. apply (proj2 (outStExc_put _ _ _)). reflexivity.
    + right. apply (proj2 (outStExc_diverge _ _)). reflexivity.
Qed.

(** Every run of [progB] that terminates does so in state [42]. *)
Theorem progB_dwlp_under :
  triple (@dwlpStExc nat) progB Under
    (fun _ => True)
    (fun r => match r with Some (_, s) => s = 42 | None => False end).
Proof.
  intros s _. apply (proj2 (dwlpStExc_read progB s _)). intros o Ho.
  apply progB_out in Ho. destruct Ho as [Ho|Ho]; subst o; cbn;
    [ reflexivity | exact I ].
Qed.

(** From every start state, some run of [progB] diverges. *)
Theorem progB_awlp_under :
  triple (@awlpStExc nat) progB Under (fun _ => True) (fun _ => False).
Proof.
  intros s _. apply (proj2 (awlpStExc_read progB s _)).
  exists None. split; [ apply progB_out; right; reflexivity | exact I ].
Qed.

