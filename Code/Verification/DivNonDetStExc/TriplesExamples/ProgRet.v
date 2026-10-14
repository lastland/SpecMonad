(** * [progRet]: [ret tt]

    The state is unchanged.  Seven triples: DWP, DWLP, AWLP, DSP and ASLP
    [Over]; DSP and ASLP [Under]. *)

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

Definition progRet : stdivexcndNE nat unit := ret tt.

Lemma progRet_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progRet s o <-> o = Some (Some (tt, s)).
Proof. exact (outStExc_ret tt s o). Qed.

(** If every run of [progRet] ends in state [0], it started there. *)
Theorem progRet_dwp_over :
  triple (@dwpStExc nat) progRet Over preEq0 postEq0.
Proof.
  intros s H.
  pose proof (proj1 (dwpStExc_read progRet s _) H) as H'.
  clear H. rename H' into H.
  specialize (H (Some (Some (tt, s))) (proj2 (progRet_out s _) eq_refl)).
  injection H as Hs. exact Hs.
Qed.

Theorem progRet_dwlp_over :
  triple (@dwlpStExc nat) progRet Over preEq0 postEq0.
Proof.
  intros s H.
  pose proof (proj1 (dwlpStExc_read progRet s _) H) as H'.
  clear H. rename H' into H.
  specialize (H (Some (Some (tt, s))) (proj2 (progRet_out s _) eq_refl)).
  injection H as Hs. exact Hs.
Qed.

Theorem progRet_awlp_over :
  triple (@awlpStExc nat) progRet Over preEq0 postEq0.
Proof.
  intros s H.
  pose proof (proj1 (awlpStExc_read progRet s _) H) as H'.
  clear H. rename H' into H.
  destruct H as [o [Ho Hq]]. apply (proj1 (progRet_out _ _)) in Ho. subst o.
  injection Hq as Hs. exact Hs.
Qed.

Theorem progRet_dsp_under :
  triple (@dspStExc nat) progRet Under preEq0 postEq0.
Proof.
  intros r Hr. unfold postEq0 in Hr. subst r.
  apply (proj2 (dspStExc_read progRet preEq0 _)). split.
  - exists 0. split; [ reflexivity | apply (proj2 (progRet_out _ _)); reflexivity ].
  - intros s Ho. apply (proj1 (progRet_out _ _)) in Ho. injection Ho as Hs.
    unfold preEq0. exact (eq_sym Hs).
Qed.

Theorem progRet_dsp_over :
  triple (@dspStExc nat) progRet Over preEq0 postEq0.
Proof.
  intros r H.
  pose proof (proj1 (dspStExc_read progRet preEq0 r) H) as H'.
  clear H. rename H' into H.
  destruct H as [[s [Hs Ho]] _]. apply (proj1 (progRet_out _ _)) in Ho.
  unfold preEq0 in Hs. subst s. injection Ho as Hr. exact Hr.
Qed.

Theorem progRet_aslp_under :
  triple (@aslpStExc nat) progRet Under preEq0 postEq0.
Proof.
  intros r Hr. unfold postEq0 in Hr. subst r.
  apply (proj2 (aslpStExc_read progRet preEq0 _)). left.
  exists 0. split; [ reflexivity | apply (proj2 (progRet_out _ _)); reflexivity ].
Qed.

(** A raised exception is no result of [progRet], so it has no start state
    at all, and the liberal reading admits it. *)
Theorem progRet_aslp_over :
  triple (@aslpStExc nat) progRet Over preEq0
    (fun r => r = Some (tt, 0) \/ r = None).
Proof.
  intros r H.
  pose proof (proj1 (aslpStExc_read progRet preEq0 r) H) as H'.
  clear H. rename H' into H.
  destruct H as [[s [Hs Ho]] | H].
  - apply (proj1 (progRet_out _ _)) in Ho. unfold preEq0 in Hs. subst s.
    injection Ho as Hr. left. exact Hr.
  - destruct r as [[[] s]|]; [| right; reflexivity ].
    specialize (H s (proj2 (progRet_out s _) eq_refl)).
    unfold preEq0 in H. subst s. left. reflexivity.
Qed.

