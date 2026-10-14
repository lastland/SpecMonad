(** * Loops that never exit

    [forever m] runs [m] again and again; [silentLoop] continues without
    doing anything.  Neither has a finite run, so every demonic liberal
    triple holds of them ([forever_dwlp], [silentLoop_dwlp]) and no demonic
    total one does ([forever_not_dwp], [silentLoop_not_dwp]).  In general, a
    program none of whose runs terminates has no total-correctness triple
    ([dwp_no_loops]): it has an outcome, which is divergence. *)

From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Basics Basics.Monad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

(** A program none of whose runs terminates satisfies no total-correctness
    triple with a satisfiable precondition. *)
Theorem dwp_no_loops {A} (d : divndNE A) (P : unit -> Prop) (Q : A -> Prop) :
  P tt ->
  triple (@dwlpPure) d Under P (fun _ => False) ->
  ~ triple (@dwpPure) d Under P Q.
Proof.
  intros Hp Hl Ht.
  pose proof (proj1 (dwlpPure_read d _) (Hl tt Hp)) as Hl'.
  pose proof (proj1 (dwpPure_read d _) (Ht tt Hp)) as Ht'.
  destruct (getNE_nonEmpty d) as [[a|] Ho]; [ exact (Hl' _ Ho) | exact (Ht' _ Ho) ].
Qed.

(* ================================================================= *)
(** * [forever m]                                                     *)
(* ================================================================= *)

(** Run [m] forever, ignoring its result. *)
Definition forever (m : divndNE unit) : divndNE unit :=
  iter (fun _ : unit => m ;; ret (inl tt)) tt.

(** The only outcome of [forever m] is divergence. *)
Lemma forever_out (m : divndNE unit) (o : option unit) :
  unOptionT (getNE (forever m)) o <-> o = None.
Proof.
  assert (Hfin : forall o, unOptionT (getNE (forever m)) o -> o = None).
  { intros o' Ho. apply (proj1 (outcomes_iter _ _ _)) in Ho.
    destruct Ho as [Ho | [Ho _]]; [| exact Ho ].
    refine (iterOut_invariant _ (fun _ => True) (fun o => o = None) _ tt o' I Ho).
    intros [] o1 _ Hs. apply (proj1 (outcomes_bind _ _ _)) in Hs.
    destruct Hs as [o2 [_ Hk]].
    destruct o2 as [[]|]; cbn in Hk; subst o1; [ exact I | reflexivity ]. }
  split; [ exact (Hfin o) |].
  intros ->. destruct (getNE_nonEmpty (forever m)) as [o0 Ho0].
  rewrite (Hfin o0 Ho0) in Ho0. exact Ho0.
Qed.

(** [DWLP] accepts [forever m], whatever the postcondition. *)
Theorem forever_dwlp (m : divndNE unit) (P : unit -> Prop) (Q : unit -> Prop) :
  triple (@dwlpPure) (forever m) Under P Q.
Proof.
  intros [] _. apply (proj2 (dwlpPure_read _ _)).
  intros o Ho. apply forever_out in Ho. subst o. exact I.
Qed.

(** [DWP] rejects it. *)
Theorem forever_not_dwp (m : divndNE unit) (P : unit -> Prop) (Q : unit -> Prop) :
  P tt -> ~ triple (@dwpPure) (forever m) Under P Q.
Proof.
  intros Hp H.
  exact (proj1 (dwpPure_read _ _) (H tt Hp) None (proj2 (forever_out m None) eq_refl)).
Qed.

(** The same, through [dwp_no_loops]. *)
Example forever_not_dwp' (m : divndNE unit) (P : unit -> Prop) (Q : unit -> Prop) :
  P tt -> ~ triple (@dwpPure) (forever m) Under P Q.
Proof.
  intro Hp. exact (dwp_no_loops (forever m) P Q Hp (forever_dwlp m P (fun _ => False))).
Qed.

(* ================================================================= *)
(** * [silentLoop]                                                    *)
(* ================================================================= *)

(** Continue, doing nothing. *)
Definition silentLoop : divndNE unit :=
  iter (fun _ : unit => ret (inl tt)) tt.

(** [silentLoop] has the outcomes of [divergeNE]. *)
Lemma silentLoop_out (o : option unit) :
  unOptionT (getNE silentLoop) o <-> unOptionT (getNE divergeNE) o.
Proof.
  unfold silentLoop. rewrite outcomes_iter.
  change (unOptionT (getNE divergeNE) o) with (o = None). split.
  - intros [Ho | [Ho _]]; [| exact Ho ].
    refine (iterOut_invariant _ (fun _ => True) (fun o => o = None) _ tt o I Ho).
    intros [] o1 _ Hs. cbn in Hs. subst o1. exact I.
  - intros ->. right. split; [ reflexivity |].
    refine (loopsForever_recurrence _ (fun _ => True) _ tt I).
    intros [] _. exists tt. split; [ reflexivity | exact I ].
Qed.

(** [DWP] rejects [silentLoop]. *)
Theorem silentLoop_not_dwp (P : unit -> Prop) (Q : unit -> Prop) :
  P tt -> ~ triple (@dwpPure) silentLoop Under P Q.
Proof.
  intros Hp H.
  exact (proj1 (dwpPure_read _ _) (H tt Hp) None (proj2 (silentLoop_out None) eq_refl)).
Qed.

(** [DWLP] accepts it, whatever the postcondition. *)
Theorem silentLoop_dwlp (P : unit -> Prop) (Q : unit -> Prop) :
  triple (@dwlpPure) silentLoop Under P Q.
Proof.
  intros [] _. apply (proj2 (dwlpPure_read _ _)).
  intros o Ho. apply silentLoop_out in Ho. cbn in Ho. subst o. exact I.
Qed.
