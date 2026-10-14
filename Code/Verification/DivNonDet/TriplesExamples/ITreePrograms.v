(** * Programs as interaction trees

    Programs written with the ITree library's definitions, over its
    nondeterministic choice [nondetE] ([Nondeterminism.or], [ITree.spin]),
    and verified through [denote]:

      [oneOrTwoIT]      a choice between returning [1] and [2];
      [ITree.spin]      the silent loop: DWLP accepts it, DWP rejects it;
      [countdownIT n]   the loop of [Countdown.v], built with [ITree.iter].

    [countdownIT n] has the outcomes of [countdown n] ([countdownIT_out],
    by [denote_iter]), so it has exactly the triples of [countdown n], for
    each of the eight readings ([countdownIT_dwp] &c.). *)

From ExtLib Require Import Monad OptionMonad.
From ITree Require Import ITree.
From ITree Require Events.Nondeterminism.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.
From Incorrectness.Verification.DivNonDet.TriplesExamples Require Import Countdown.

(* ================================================================= *)
(** * A choice                                                        *)
(* ================================================================= *)

Definition oneOrTwoIT : itree Nondeterminism.nondetE nat := Nondeterminism.or (Ret 1) (Ret 2).

Lemma oneOrTwoIT_out (o : option nat) :
  unOptionT (getNE (denote oneOrTwoIT)) o <-> o = Some 1 \/ o = Some 2.
Proof. unfold oneOrTwoIT. rewrite denote_or, !denote_ret. reflexivity. Qed.

(** Every run returns [1] or [2]. *)
Theorem oneOrTwoIT_dwp_under :
  triple (@dwpPure ∘ₘₘ @denote _ _) oneOrTwoIT Under (fun _ => True) (fun a => a = 1 \/ a = 2).
Proof.
  intros [] _. apply (proj2 (dwpPure_read _ _)). intros o Ho.
  apply oneOrTwoIT_out in Ho. destruct Ho as [-> | ->]; [ left | right ]; reflexivity.
Qed.

(** The result [1] is reached: an incorrectness triple. *)
Theorem oneOrTwoIT_asp_under :
  triple (@aspPure ∘ₘₘ @denote _ _) oneOrTwoIT Under (fun _ => True) (fun a => a = 1).
Proof.
  intros a ->. apply (proj2 (aspPure_read _ _ _)).
  split; [ exact I | apply oneOrTwoIT_out; left; reflexivity ].
Qed.

(* ================================================================= *)
(** * The silent loop                                                 *)
(* ================================================================= *)

Theorem spin_not_dwp (P : unit -> Prop) (Q : unit -> Prop) :
  P tt -> ~ triple (@dwpPure ∘ₘₘ @denote _ _) (ITree.spin : itree Nondeterminism.nondetE unit) Under P Q.
Proof.
  intros Hp H.
  exact (proj1 (dwpPure_read _ _) (H tt Hp) None (proj2 (denote_spin None) eq_refl)).
Qed.

Theorem spin_dwlp (P : unit -> Prop) (Q : unit -> Prop) :
  triple (@dwlpPure ∘ₘₘ @denote _ _) (ITree.spin : itree Nondeterminism.nondetE unit) Under P Q.
Proof.
  intros [] _. apply (proj2 (dwlpPure_read _ _)).
  intros o Ho. apply denote_spin in Ho. subst o. exact I.
Qed.

(* ================================================================= *)
(** * [countdownIT n]                                                 *)
(* ================================================================= *)

Definition countdownBodyIT (n : nat) : itree Nondeterminism.nondetE (nat + nat) :=
  match n with
  | 0 => Ret (inr 0)
  | 1 => Ret (inl 1)
  | S (S k) => Nondeterminism.or (Ret (inl k)) (Ret (inl (S k)))
  end.

Definition countdownIT (n : nat) : itree Nondeterminism.nondetE nat := ITree.iter countdownBodyIT n.

Lemma countdownBodyIT_out (n : nat) (o : option (nat + nat)) :
  unOptionT (getNE (denote (countdownBodyIT n))) o
  <-> unOptionT (getNE (countdownBody n)) o.
Proof.
  rewrite countdown_step. destruct n as [|[|k]]; cbn [countdownBodyIT];
    [ rewrite denote_ret | rewrite denote_ret | rewrite denote_or, !denote_ret ];
    reflexivity.
Qed.

Lemma countdownIT_out (n : nat) (o : option nat) :
  unOptionT (getNE (denote (countdownIT n))) o <-> unOptionT (getNE (countdown n)) o.
Proof.
  unfold countdownIT, countdown. rewrite denote_iter, !outcomes_iter.
  apply iterOutcomes_ext. intros j o'. apply countdownBodyIT_out.
Qed.

(** The triples of [countdownIT n] are those of [countdown n]. *)

Theorem countdownIT_dwp (n : nat) k P Q :
  triple (@dwpPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@dwpPure) (countdown n) k P Q.
Proof. exact (triple_dwpPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_dwlp (n : nat) k P Q :
  triple (@dwlpPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@dwlpPure) (countdown n) k P Q.
Proof. exact (triple_dwlpPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_awp (n : nat) k P Q :
  triple (@awpPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@awpPure) (countdown n) k P Q.
Proof. exact (triple_awpPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_awlp (n : nat) k P Q :
  triple (@awlpPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@awlpPure) (countdown n) k P Q.
Proof. exact (triple_awlpPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_asp (n : nat) k P Q :
  triple (@aspPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@aspPure) (countdown n) k P Q.
Proof. exact (triple_aspPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_dslp (n : nat) k P Q :
  triple (@dslpPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@dslpPure) (countdown n) k P Q.
Proof. exact (triple_dslpPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_dsp (n : nat) k P Q :
  triple (@dspPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@dspPure) (countdown n) k P Q.
Proof. exact (triple_dspPure_same _ _ (countdownIT_out n) k P Q). Qed.

Theorem countdownIT_aslp (n : nat) k P Q :
  triple (@aslpPure ∘ₘₘ @denote _ _) (countdownIT n) k P Q <-> triple (@aslpPure) (countdown n) k P Q.
Proof. exact (triple_aslpPure_same _ _ (countdownIT_out n) k P Q). Qed.

(** For instance: if every run of [countdownIT n] terminates, [n = 0];
    from an input of at least [2], the result [0] is reached. *)

Example countdownIT_dwp_over (n : nat) :
  triple (@dwpPure ∘ₘₘ @denote _ _) (countdownIT n) Over (fun _ => n = 0) (fun _ => True).
Proof. apply countdownIT_dwp. exact (countdown_dwp_over n). Qed.

Example countdownIT_asp_under (n : nat) :
  2 <= n -> triple (@aspPure ∘ₘₘ @denote _ _) (countdownIT n) Under (fun _ => True) (fun r => r = 0).
Proof. intro Hn. apply countdownIT_asp. exact (countdown_asp_under n Hn). Qed.
