(** * [countdown n]: a loop that terminates for some inputs and not others

    While the counter is not [0]: at [1] do nothing, otherwise subtract [2]
    or [1], nondeterministically.  The result is the final counter.

      from [0]          every run terminates at once, with [0];
      from [1]          every run loops forever;
      from [2] and up   some run terminates with [0] (it avoids [1]), and
                        some run loops forever (it steps onto [1]).

    The base setting has one start point, [tt], so the input is the
    parameter [n] and a precondition is a proposition about it.  With a
    single start point the SP readings say less than with state: "reached
    from a start in [P]" is "[P] holds and the result is reached".

    The outcomes ([countdown_out]) follow from the loop rules of
    [Computation.v]: an invariant for the results, a variant for the absence
    of infinite runs from [0], reaching for the runs that terminate, and
    recurrence for those that do not.  Each of the sixteen triples below is
    read off them. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Basics Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.

Definition countdownBody (n : nat) : divndNE (nat + nat) :=
  match n with
  | 0 => ret (inr 0)
  | 1 => ret (inl 1)
  | S (S k) => orNE (ret (inl k)) (ret (inl (S k)))
  end.

Definition countdown (n : nat) : divndNE nat := iter countdownBody n.

(* ================================================================= *)
(** * The outcomes                                                    *)
(* ================================================================= *)

(** One iteration, from counter [n]. *)
Lemma countdown_step (n : nat) (o : option (nat + nat)) :
  unOptionT (getNE (countdownBody n)) o
  <-> match n with
      | 0 => o = Some (inr 0)
      | 1 => o = Some (inl 1)
      | S (S k) => o = Some (inl k) \/ o = Some (inl (S k))
      end.
Proof. destruct n as [|[|k]]; reflexivity. Qed.

(** From [0] or [2] and up some run terminates, always with [0]; from [1]
    and up some run loops forever. *)
Lemma countdown_out (n : nat) (o : option nat) :
  unOptionT (getNE (countdown n)) o
  <-> (n <> 1 /\ o = Some 0) \/ (1 <= n /\ o = None).
Proof.
  unfold countdown. rewrite outcomes_iter. unfold iterOutcomes. split.
  - intros [Ho | [-> Hloop]].
    + left. split.
      * (* invariant: from [1] the counter stays at [1], so nothing ends *)
        intros ->.
        refine (iterOut_invariant _ (fun j => j = 1) (fun _ => False) _ 1 o eq_refl Ho).
        intros j o1 Hj Hs. subst j.
        apply countdown_step in Hs. cbv beta iota in Hs. subst o1. reflexivity.
      * (* invariant: the loop only exits with [0] *)
        refine (iterOut_invariant _ (fun _ => True) (fun o => o = Some 0) _ n o I Ho).
        intros j o1 _ Hs. apply countdown_step in Hs.
        destruct j as [|[|k]]; cbv beta iota in Hs;
          [ subst o1; reflexivity | subst o1; exact I |].
        destruct Hs as [-> | ->]; exact I.
    + right. split; [| reflexivity ].
      (* variant: from [0] there is no next iteration *)
      destruct n as [|n]; [ exfalso | lia ].
      refine (loopsForever_variant _ (fun j => j = 0) (fun j => j) _ 0 eq_refl Hloop).
      intros j j' Hj Hs. subst j.
      apply countdown_step in Hs. discriminate.
  - intros [[Hn ->] | [Hn ->]].
    + left.
      (* reaching [0], by a decreasing counter that avoids [1] *)
      enough (H : exists o, o = Some 0
                            /\ iterOut (fun j => unOptionT (getNE (countdownBody j))) n o)
        by (destruct H as [o [-> Ho]]; exact Ho).
      apply (iterOut_reach _ (fun j => j <> 1) (fun j => j) (fun o => o = Some 0));
        [| exact Hn ].
      intros j Hj. destruct j as [|[|k]].
      * exists (Some (inr 0)). split; [ apply countdown_step; reflexivity | reflexivity ].
      * contradiction.
      * destruct (Nat.eq_dec k 1) as [-> | Hk].
        -- exists (Some (inl 2)).
           split; [ apply countdown_step; right; reflexivity | cbn; lia ].
        -- exists (Some (inl k)).
           split; [ apply countdown_step; left; reflexivity | cbn; lia ].
    + right. split; [ reflexivity |].
      (* recurrence: a positive counter can step to a positive counter *)
      refine (loopsForever_recurrence _ (fun j => 1 <= j) _ n Hn).
      intros j Hj. destruct j as [|[|k]].
      * lia.
      * exists 1. split; [ apply countdown_step; reflexivity | lia ].
      * exists (S k). split; [ apply countdown_step; right; reflexivity | lia ].
Qed.

(** The result [0] is reached from every input other than [1]. *)
Lemma countdown_reaches_0 (n : nat) :
  n <> 1 -> unOptionT (getNE (countdown n)) (Some 0).
Proof. intro Hn. apply countdown_out. left. split; [ exact Hn | reflexivity ]. Qed.

(** Every input from [1] up may loop forever. *)
Lemma countdown_may_loop (n : nat) :
  1 <= n -> unOptionT (getNE (countdown n)) None.
Proof. intro Hn. apply countdown_out. right. split; [ exact Hn | reflexivity ]. Qed.

(* ================================================================= *)
(** * WP                                                              *)
(* ================================================================= *)

(** From [0], every run terminates, with [0]. *)
Theorem countdown_dwp_under (n : nat) :
  triple (@dwpPure) (countdown n) Under (fun _ => n = 0) (fun r => r = 0).
Proof.
  intros [] Hn. apply (proj2 (dwpPure_read _ _)). intros o Ho.
  apply countdown_out in Ho. destruct Ho as [[_ ->] | [Hl _]]; [ reflexivity | lia ].
Qed.

(** If every run terminates, the input was [0]: no other input is safe for
    total correctness. *)
Theorem countdown_dwp_over (n : nat) :
  triple (@dwpPure) (countdown n) Over (fun _ => n = 0) (fun _ => True).
Proof.
  intros [] H. pose proof (proj1 (dwpPure_read _ _) H) as H'. clear H.
  destruct n as [|n]; [ reflexivity | exfalso ].
  exact (H' None (countdown_may_loop (S n) ltac:(lia))).
Qed.

(** Every run that terminates ends with [0]. *)
Theorem countdown_dwlp_under (n : nat) :
  triple (@dwlpPure) (countdown n) Under (fun _ => True) (fun r => r = 0).
Proof.
  intros [] _. apply (proj2 (dwlpPure_read _ _)). intros o Ho.
  apply countdown_out in Ho. destruct Ho as [[_ ->] | [_ ->]]; reflexivity.
Qed.

(** If no run terminates, the input was [1]. *)
Theorem countdown_dwlp_over (n : nat) :
  triple (@dwlpPure) (countdown n) Over (fun _ => n = 1) (fun _ => False).
Proof.
  intros [] H. pose proof (proj1 (dwlpPure_read _ _) H) as H'. clear H.
  destruct (Nat.eq_dec n 1) as [Hn | Hn]; [ exact Hn | exfalso ].
  exact (H' _ (countdown_reaches_0 n Hn)).
Qed.

(** From every input other than [1], some run terminates with [0]. *)
Theorem countdown_awp_under (n : nat) :
  triple (@awpPure) (countdown n) Under (fun _ => n <> 1) (fun r => r = 0).
Proof.
  intros [] Hn. apply (proj2 (awpPure_read _ _)).
  exists (Some 0). split; [ exact (countdown_reaches_0 n Hn) | reflexivity ].
Qed.

(** If some run terminates, the input was not [1]. *)
Theorem countdown_awp_over (n : nat) :
  triple (@awpPure) (countdown n) Over (fun _ => n <> 1) (fun _ => True).
Proof.
  intros [] H. pose proof (proj1 (awpPure_read _ _) H) as H'. clear H.
  destruct H' as [o [Ho Hq]]. apply countdown_out in Ho.
  destruct Ho as [[Hn _] | [_ ->]]; [ exact Hn | contradiction ].
Qed.

(** From every positive input, some run loops forever. *)
Theorem countdown_awlp_under (n : nat) :
  triple (@awlpPure) (countdown n) Under (fun _ => 1 <= n) (fun _ => False).
Proof.
  intros [] Hn. apply (proj2 (awlpPure_read _ _)).
  exists None. split; [ exact (countdown_may_loop n Hn) | exact I ].
Qed.

(** If some run loops forever, the input was positive. *)
Theorem countdown_awlp_over (n : nat) :
  triple (@awlpPure) (countdown n) Over (fun _ => 1 <= n) (fun _ => False).
Proof.
  intros [] H. pose proof (proj1 (awlpPure_read _ _) H) as H'. clear H.
  destruct H' as [o [Ho Hq]]. apply countdown_out in Ho.
  destruct Ho as [[_ ->] | [Hn _]]; [ contradiction | exact Hn ].
Qed.

(* ================================================================= *)
(** * SP                                                              *)
(* ================================================================= *)

(** From an input of at least [2], where the loop may also run forever,
    the result [0] is reached: an incorrectness triple. *)
Theorem countdown_asp_under (n : nat) :
  2 <= n -> triple (@aspPure) (countdown n) Under (fun _ => True) (fun r => r = 0).
Proof.
  intros Hn r Hr. subst r. apply (proj2 (aspPure_read _ _ _)).
  split; [ exact I | apply countdown_reaches_0; lia ].
Qed.

(** Every result is [0]. *)
Theorem countdown_asp_over (n : nat) :
  triple (@aspPure) (countdown n) Over (fun _ => True) (fun r => r = 0).
Proof.
  intros r H. destruct (proj1 (aspPure_read _ _ _) H) as [_ Ho].
  apply countdown_out in Ho.
  destruct Ho as [[_ Ho] | [_ Ho]]; [ injection Ho as Hr; exact Hr | discriminate ].
Qed.

(** If [0] is reached, the input was not [1]. *)
Theorem countdown_dslp_under (n : nat) :
  triple (@dslpPure) (countdown n) Under (fun _ => n <> 1) (fun r => r = 0).
Proof.
  intros r Hr. subst r. apply (proj2 (dslpPure_read _ _ _)).
  intro Ho. apply countdown_out in Ho.
  destruct Ho as [[Hn _] | [_ Ho]]; [ exact Hn | discriminate ].
Qed.

(** From an input other than [1], a result that is never reached is not
    [0]: [0] is reached. *)
Theorem countdown_dslp_over (n : nat) :
  n <> 1 -> triple (@dslpPure) (countdown n) Over (fun _ => False) (fun r => r <> 0).
Proof.
  intros Hn r H Hr. subst r.
  exact (proj1 (dslpPure_read _ _ _) H (countdown_reaches_0 n Hn)).
Qed.

(** From an input other than [1], [0] is reached, and only when the input
    is not [1]. *)
Theorem countdown_dsp_under (n : nat) :
  n <> 1 -> triple (@dspPure) (countdown n) Under (fun _ => n <> 1) (fun r => r = 0).
Proof.
  intros Hn r Hr. subst r. apply (proj2 (dspPure_read _ _ _)).
  split; [ split; [ exact Hn | exact (countdown_reaches_0 n Hn) ] | intros _; exact Hn ].
Qed.

(** A result reached when the input is not [1], and only then, is [0]. *)
Theorem countdown_dsp_over (n : nat) :
  triple (@dspPure) (countdown n) Over (fun _ => n <> 1) (fun r => r = 0).
Proof.
  intros r H. destruct (proj1 (dspPure_read _ _ _) H) as [[_ Ho] _].
  apply countdown_out in Ho.
  destruct Ho as [[_ Ho] | [_ Ho]]; [ injection Ho as Hr; exact Hr | discriminate ].
Qed.

(** Every result is reached only when the input is not [1]. *)
Theorem countdown_aslp_under (n : nat) :
  triple (@aslpPure) (countdown n) Under (fun _ => n <> 1) (fun _ => True).
Proof.
  intros r _. apply (proj2 (aslpPure_read _ _ _)). right.
  intro Ho. apply countdown_out in Ho.
  destruct Ho as [[Hn _] | [_ Ho]]; [ exact Hn | discriminate ].
Qed.

(** From an input other than [1], a result reached from input [1], or only
    from it, is not [0]. *)
Theorem countdown_aslp_over (n : nat) :
  n <> 1 -> triple (@aslpPure) (countdown n) Over (fun _ => n = 1) (fun r => r <> 0).
Proof.
  intros Hn r H Hr. subst r.
  destruct (proj1 (aslpPure_read _ _ _) H) as [[H1 _] | H'].
  - exact (Hn H1).
  - exact (Hn (H' (countdown_reaches_0 n Hn))).
Qed.
