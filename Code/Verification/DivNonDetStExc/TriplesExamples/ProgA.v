(** * [progA]: put [42], then keep it or add [1]

    Every run terminates, in state [42] or [43].  Six triples: DWP, AWP
    and ASP [Under]; AWP, ASP and DSLP [Over]. *)

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

Definition progA : stdivexcndNE nat unit :=
  put 42 ;;
  s <- get ;;
  orStExc (put s) (put (s + 1)).

Lemma progA_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progA s o <-> o = Some (Some (tt, 42)) \/ o = Some (Some (tt, 43)).
Proof.
  unfold progA. split.
  - intro H. apply (proj1 (outStExc_bind _ _ _ _)) in H. destruct H as [o1 [H1 H2]].
    apply (proj1 (outStExc_put _ _ _)) in H1. subst o1. cbn beta iota in H2.
    apply (proj1 (outStExc_bind _ _ _ _)) in H2. destruct H2 as [o2 [H2 H3]].
    apply (proj1 (outStExc_get _ _)) in H2. subst o2. cbn beta iota in H3.
    apply (proj1 (outStExc_or _ _ _ _)) in H3.
    destruct H3 as [H3|H3]; apply (proj1 (outStExc_put _ _ _)) in H3; subst o;
      [ left | right ]; reflexivity.
  - intro H. apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (tt, 42))).
    split; [ apply (proj2 (outStExc_put _ _ _)); reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_bind _ _ _ _)). exists (Some (Some (42, 42))).
    split; [ apply (proj2 (outStExc_get _ _)); reflexivity |]. cbn beta iota.
    apply (proj2 (outStExc_or _ _ _ _)).
    destruct H as [H|H]; subst o; [ left | right ]; apply (proj2 (outStExc_put _ _ _));
      reflexivity.
Qed.

(** Every run of [progA] terminates with a state of at least [42]. *)
Theorem progA_dwp_under :
  triple (@dwpStExc nat) progA Under
    (fun _ => True)
    (fun r => match r with Some (_, s) => s >= 42 | None => False end).
Proof.
  intros s _. apply (proj2 (dwpStExc_read progA s _)). intros o Ho.
  apply progA_out in Ho. destruct Ho as [Ho|Ho]; subst o; cbn; lia.
Qed.

(** Some run of [progA] ends in state [42]. *)
Theorem progA_awp_under :
  triple (@awpStExc nat) progA Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  intros s _. apply (proj2 (awpStExc_read progA s _)).
  exists (Some (Some (tt, 42))).
  split; [ apply progA_out; left; reflexivity | reflexivity ].
Qed.

(** No run of [progA] ends in state [100]. *)
Theorem progA_awp_over :
  triple (@awpStExc nat) progA Over
    (fun _ => False)
    (fun r => r = Some (tt, 100)).
Proof.
  intros s H.
  pose proof (proj1 (awpStExc_read progA s _) H) as H'.
  clear H. rename H' into H.
  destruct H as [o [Ho Hq]]. apply progA_out in Ho.
  destruct Ho as [Ho|Ho]; subst o; discriminate Hq.
Qed.

(** Every result of [progA] has a state of at least [42]. *)
Theorem progA_asp_over :
  triple (@aspStExc nat) progA Over
    (fun _ => True)
    (fun r => match r with Some (_, s') => s' >= 42 | None => False end).
Proof.
  intros r H.
  pose proof (proj1 (aspStExc_read progA (fun _ : nat => True) r) H) as H'.
  clear H. rename H' into H.
  destruct H as [s [_ Ho]]. apply progA_out in Ho.
  destruct Ho as [Ho|Ho]; injection Ho as Hr; subst r; cbn; lia.
Qed.

(** The state [42] is reached: an incorrectness triple. *)
Theorem progA_asp_under :
  triple (@aspStExc nat) progA Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  intros r Hr. subst r. apply (proj2 (aspStExc_read progA (fun _ : nat => True) _)).
  exists 0. split; [ exact I | apply progA_out; left; reflexivity ].
Qed.

(** A result all of whose start states are [0] is not the state [42], which
    [progA] reaches from every start state. *)
Theorem progA_dslp_over :
  triple (@dslpStExc nat) progA Over preEq0 (fun r => r <> Some (tt, 42)).
Proof.
  intros r H Hr. subst r.
  pose proof (proj1 (dslpStExc_read progA preEq0 _) H) as H'.
  clear H. rename H' into H.
  specialize (H 1 (proj2 (progA_out 1 _) (or_introl eq_refl))).
  discriminate H.
Qed.

