(** * Example programs, and a verified triple of each kind

    The programs are written in the state-and-exceptions monad
    [stdivexcndNE nat].  An outcome from a start state is divergence, a
    raised exception, or a result with its final state; each program comes
    with the set of its outcomes ([progA_out] &c.), and every triple below is
    read off that set.

    One example for each of the sixteen kinds of triple:

                  [Under]                  [Over]
      DWP    [progA_dwp_under]        [progRet_dwp_over]
      DWLP   [progB_dwlp_under]       [progRet_dwlp_over]
      AWP    [progA_awp_under]        [progA_awp_over]
      AWLP   [progB_awlp_under]       [progRet_awlp_over]
      ASP    [progA_asp_under]        [progA_asp_over]
      DSLP   [progEx_dslp_under]      [progA_dslp_over]
      DSP    [progRet_dsp_under]      [progRet_dsp_over]
      ASLP   [progRet_aslp_under]     [progRet_aslp_over]

    A WP [Under] triple says the precondition is included in [wp] of the
    postcondition; an SP [Under] triple says the postcondition is included
    in [sp] of the precondition, which for ASP is an incorrectness triple.

    Two further programs contrast the two readings of "a bug is reachable":
    [progloom_awp_under] (from EVERY start state satisfying the
    precondition, some run raises) against [progloom_asp_under] (the raise
    is reached from SOME such state), and their failure and success on
    [progloom_harder].  [example_incorrect] is Example 3.1 of O'Hearn's
    "Incorrectness Logic". *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** * The programs and their outcomes                                 *)
(* ================================================================= *)

Definition progA : stdivexcndNE nat unit :=
  put 42 ;;
  s <- get ;;
  orStExc (put s) (put (s + 1)).

Definition progB : stdivexcndNE nat unit :=
  put 42 ;;
  s <- get ;;
  orStExc (put s) divergeStExc.

Definition progRet : stdivexcndNE nat unit := ret tt.

Definition progEx : stdivexcndNE nat unit :=
  s <- get ;;
  orStExc (put (s + 1)) (put 42).

(** O'Hearn, "Incorrectness Logic", Example 3.1: set [z] to [42] when [x] is
    even and [y] is odd; otherwise leave the state alone. *)
Definition example_state : stdivexcndNE (nat * nat * nat) unit :=
  s <- get ;;
  let '(x, y, _) := s in
  if Nat.even x then
    if negb (Nat.even y) then put (x, y, 42) else ret tt
  else ret tt.

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

Definition preEq0 : nat -> Prop := fun s => s = 0.
Definition postEq0 : option (unit * nat) -> Prop := fun r => r = Some (tt, 0).

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

Lemma progRet_out (s : nat) (o : option (option (unit * nat))) :
  outStExc progRet s o <-> o = Some (Some (tt, s)).
Proof. exact (outStExc_ret tt s o). Qed.

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

(* ================================================================= *)
(** * WP                                                              *)
(* ================================================================= *)

(** Every run of [progA] terminates with a state of at least [42]. *)
Theorem progA_dwp_under :
  triple (@dwpStExc nat) progA Under
    (fun _ => True)
    (fun r => match r with Some (_, s) => s >= 42 | None => False end).
Proof.
  intros s _. apply (proj2 (dwpStExc_read progA s _)). intros o Ho.
  apply progA_out in Ho. destruct Ho as [Ho|Ho]; subst o; cbn; lia.
Qed.

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

Theorem progRet_dwlp_over :
  triple (@dwlpStExc nat) progRet Over preEq0 postEq0.
Proof.
  intros s H.
  pose proof (proj1 (dwlpStExc_read progRet s _) H) as H'.
  clear H. rename H' into H.
  specialize (H (Some (Some (tt, s))) (proj2 (progRet_out s _) eq_refl)).
  injection H as Hs. exact Hs.
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

(** From every start state, some run of [progB] diverges. *)
Theorem progB_awlp_under :
  triple (@awlpStExc nat) progB Under (fun _ => True) (fun _ => False).
Proof.
  intros s _. apply (proj2 (awlpStExc_read progB s _)).
  exists None. split; [ apply progB_out; right; reflexivity | exact I ].
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

(* ================================================================= *)
(** * SP                                                              *)
(* ================================================================= *)

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

(** The state [1] is reached by [progEx] only from [0]. *)
Theorem progEx_dslp_under :
  triple (@dslpStExc nat) progEx Under preEq0 (fun r => r = Some (tt, 1)).
Proof.
  intros r Hr. subst r. apply (proj2 (dslpStExc_read progEx preEq0 _)).
  intros s Ho. apply progEx_out in Ho. unfold preEq0.
  destruct Ho as [Ho|Ho]; injection Ho as Hs; lia.
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

(* ================================================================= *)
(** * Reaching a bug: from every start state, or from some           *)
(* ================================================================= *)

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
