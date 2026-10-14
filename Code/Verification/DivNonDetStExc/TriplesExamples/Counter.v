(** * [counter N]: a loop whose bug is reached after many iterations

    In the style of the loop examples of O'Hearn's "Incorrectness Logic"
    (POPL 2020): a counter that, at each iteration, either stops or
    increments the state, and raises when the state reaches [N].

      from [s < N]   stops in any state from [s] to [N - 1], or raises;
                     never diverges;
      from [s >= N]  stops in any state from [s] on, never raises, and may
                     run forever.

    It is an ITree program ([stateT nat (optionT (itree nondetE))], with
    ExtLib's [get], [put], [raise] and the ITree loop), verified through
    [denoteStExc]: its tree is an [ITree.iter] whose body has the outcomes
    of [counterStep] ([counter_iter], by [denote_iter]), and the loop rules
    of [DivNonDet/Computation.v] give its outcomes ([counter_out]).

    The triples are those incorrectness logic is designed for:
      the bug is reachable ([counter_bug_reachable]), and every state below
      [N] is reached ([counter_all_reached]), without a loop invariant;
      paths can be dropped ([counter_drop_paths], O'Hearn's rule of
      consequence);
      a reachable bug refutes the correctness triples
      ([counter_not_correct], [counter_not_partially_correct], principle of
      denial);
    and the contrast between incorrectness logic and Lisbon logic of the
    paper ([counter_il_any_start], [counter_lisbon_fails],
    [counter_lisbon_below]), with the correctness side: total correctness
    below [N] ([counter_dwp_below]), divergence and no bug from [N] on
    ([counter_awlp_diverges], [counter_no_bug_above]).  A result [None] is
    a raised exception. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad MonadTrans.
From ITree Require Import ITree Eq Core.ITreeMonad.
From ITree Require Events.Nondeterminism.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.
From Incorrectness.Verification.DivNonDetStExc Require Import InCorrectnessPrinciples.

Import MonadNotation.
Open Scope monad_scope.

(** One iteration: stop, or increment and raise on reaching [N]. *)
Definition counterBody (N : nat) (_ : unit)
  : stateT nat (optionT (itree Nondeterminism.nondetE)) (unit + unit) :=
  b <- lift (lift (ITree.trigger Nondeterminism.Or)) ;;
  if b : bool then ret (inr tt)
  else n <- get ;; put (S n) ;;
       if Nat.eqb (S n) N then raise tt else ret (inl tt).

Definition counter (N : nat) : stateT nat (optionT (itree Nondeterminism.nondetE)) unit :=
  Basics.iter (counterBody N) tt.

(* ================================================================= *)
(** * The outcomes                                                    *)
(* ================================================================= *)

(** The body of the loop's tree, from accumulator and state [j]:
    [inr (Some r)] stops, [inr None] raises, [inl j'] continues. *)
Definition counterStep (N : nat) (j : unit * nat)
  : itree Nondeterminism.nondetE ((unit * nat) + option (unit * nat)) :=
  ITree.bind (ITree.trigger Nondeterminism.Or) (fun b : bool =>
    if b then Ret (inr (Some (tt, snd j)))
    else if Nat.eqb (S (snd j)) N then Ret (inr None) else Ret (inl (tt, S (snd j)))).

(** The program's outcomes are those of the base loop on [counterStep]. *)
Lemma counter_iter (N s : nat) (o : option (option (unit * nat))) :
  outStExc (@denoteStExc _ _ nat unit (counter N)) s o
  <-> iterOutcomes (fun j o' => unOptionT (getNE (denote (counterStep N j))) o') (tt, s) o.
Proof.
  rewrite outStExc_denoteStExc. unfold counter.
  cbv [Basics.iter MonadIter_stateT MonadIter_optionT MonadIter_itree]. cbn [runStateT unOptionT].
  rewrite denote_iter, outcomes_iter.
  apply iterOutcomes_ext. intros [[] n] o'.
  apply eq1_outcomes, (mm_proper denote_morphism).
  unfold counterStep. cbn. unfold Monad.eq1, Eq1_ITree.
  rewrite !Eqit.bind_bind. apply eutt_eq_bind. intro b.
  rewrite !Eqit.bind_ret_l. cbn [unOptionT runStateT].
  destruct b;
    repeat progress (cbn [unOptionT runStateT fst snd]; rewrite ?Eqit.bind_ret_l).
  - reflexivity.
  - destruct N as [|m]; [| destruct (Nat.eqb n m) ];
      repeat progress (cbn [unOptionT runStateT fst snd]; rewrite ?Eqit.bind_ret_l);
      reflexivity.
Qed.

Lemma counterStep_out (N n : nat) (o' : option ((unit * nat) + option (unit * nat))) :
  unOptionT (getNE (denote (counterStep N (tt, n)))) o'
  <-> o' = Some (inr (Some (tt, n)))
      \/ (S n = N /\ o' = Some (inr None))
      \/ (S n <> N /\ o' = Some (inl (tt, S n))).
Proof.
  unfold counterStep. rewrite denote_bind. unfold ITree.trigger. split.
  - intros [[b|] [Hb Ho]].
    + cbv beta in Ho. destruct b; cbn [snd] in Ho.
      * apply denote_ret in Ho. left. exact Ho.
      * destruct (Nat.eqb_spec (S n) N) as [Heq | Hne]; apply denote_ret in Ho;
          right; [ left | right ]; split; assumption.
    + apply denote_vis in Hb. destruct Hb as [x Hx]. apply denote_ret in Hx. discriminate.
  - intros [Ho | [[Heq Ho] | [Hne Ho]]];
      [ exists (Some true) | exists (Some false) | exists (Some false) ];
      (split; [ apply denote_vis; eexists; apply denote_ret; reflexivity |]);
      cbv beta; cbn [snd].
    + apply denote_ret. exact Ho.
    + rewrite (proj2 (Nat.eqb_eq _ _) Heq). apply denote_ret. exact Ho.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hne). apply denote_ret. exact Ho.
Qed.

(** From [s], the counter stops in a state [k >= s] (below [N] if [s] is),
    raises if [s < N], and may run forever if [s >= N]. *)
Lemma counter_out (N s : nat) (o : option (option (unit * nat))) :
  outStExc (@denoteStExc _ _ nat unit (counter N)) s o
  <-> (exists k, s <= k /\ (k < N \/ N <= s) /\ o = Some (Some (tt, k)))
      \/ (s < N /\ o = Some None)
      \/ (N <= s /\ o = None).
Proof.
  rewrite counter_iter. unfold iterOutcomes.
  set (step := fun j o' => unOptionT (getNE (denote (counterStep N j))) o').
  assert (Hstep : forall n o', step (tt, n) o'
                  <-> o' = Some (inr (Some (tt, n)))
                      \/ (S n = N /\ o' = Some (inr None))
                      \/ (S n <> N /\ o' = Some (inl (tt, S n))))
    by (intros n o'; apply counterStep_out).
  split.
  - intros [Ho | [-> Hloop]].
    + (* invariant: the counter never goes below [s], nor reaches [N] from below *)
      refine (iterOut_invariant step (fun j => s <= snd j /\ (snd j < N \/ N <= s))
                (fun o => (exists k, s <= k /\ (k < N \/ N <= s) /\ o = Some (Some (tt, k)))
                          \/ (s < N /\ o = Some None) \/ (N <= s /\ o = None))
                _ (tt, s) o _ Ho).
      * intros [[] n] o1 [Hsn Hn] Hs1. apply Hstep in Hs1. cbn [snd] in Hsn, Hn.
        destruct Hs1 as [-> | [[Heq ->] | [Hne ->]]]; cbv beta iota.
        -- left. exists n. split; [ exact Hsn | split; [ exact Hn | reflexivity ] ].
        -- right; left. split; [ lia | reflexivity ].
        -- cbn [snd]. split; lia.
      * cbn [snd]. split; [ lia |]. destruct (Nat.lt_ge_cases s N); [ left | right ]; assumption.
    + right; right. split; [| reflexivity ].
      destruct (Nat.lt_ge_cases s N) as [Hlt | Hge]; [ exfalso | exact Hge ].
      (* variant: below [N] the distance to [N] decreases *)
      refine (loopsForever_variant step (fun j => snd j < N) (fun j => N - snd j) _ (tt, s) Hlt Hloop).
      intros [[] n] j' Hn Hs1. apply Hstep in Hs1. cbn [snd] in Hn.
      destruct Hs1 as [Hc | [[Heq Hc] | [Hne Hc]]]; try discriminate.
      injection Hc as Hc. subst j'. cbn [snd]. lia.
  - intros [[k [Hsk [Hk ->]]] | [[Hlt ->] | [Hge ->]]].
    + left.
      (* reaching [k]: increment up to [k], then stop *)
      enough (H : exists o, o = Some (Some (tt, k)) /\ iterOut step (tt, s) o)
        by (destruct H as [o [-> Ho]]; exact Ho).
      apply (iterOut_reach step (fun j => s <= snd j <= k) (fun j => k - snd j)
               (fun o => o = Some (Some (tt, k)))); [| cbn [snd]; lia ].
      intros [[] n] Hn. cbn [snd] in Hn.
      destruct (Nat.eq_dec n k) as [-> | Hnk].
      * exists (Some (inr (Some (tt, k)))).
        split; [ apply Hstep; left; reflexivity | reflexivity ].
      * exists (Some (inl (tt, S n))).
        split; [ apply Hstep; right; right; split; [ lia | reflexivity ] | cbn [snd]; lia ].
    + left.
      (* reaching the bug: increment up to [N] *)
      enough (H : exists o, o = Some None /\ iterOut step (tt, s) o)
        by (destruct H as [o [-> Ho]]; exact Ho).
      apply (iterOut_reach step (fun j => snd j < N) (fun j => N - snd j)
               (fun o => o = Some None)); [| cbn [snd]; lia ].
      intros [[] n] Hn. cbn [snd] in Hn.
      destruct (Nat.eq_dec (S n) N) as [Heq | Hne].
      * exists (Some (inr None)).
        split; [ apply Hstep; right; left; split; [ exact Heq | reflexivity ] | reflexivity ].
      * exists (Some (inl (tt, S n))).
        split; [ apply Hstep; right; right; split; [ exact Hne | reflexivity ] | cbn [snd]; lia ].
    + right. split; [ reflexivity |].
      (* recurrence: from [N] on, incrementing never raises *)
      refine (loopsForever_recurrence step (fun j => N <= snd j) _ (tt, s) Hge).
      intros [[] n] Hn. cbn [snd] in Hn. exists (tt, S n).
      split; [ apply Hstep; right; right; split; [ lia | reflexivity ] | cbn [snd]; lia ].
Qed.

(* ================================================================= *)
(** * Incorrectness logic                                             *)
(* ================================================================= *)

(** The bug is reachable from [0]: an incorrectness triple, proved without
    a loop invariant. *)
Theorem counter_bug_reachable (N : nat) :
  0 < N ->
  triple (@aspStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => s = 0) (fun r => r = None).
Proof.
  intros HN r ->. apply (proj2 (aspStExc_read _ (fun s => s = 0) _)).
  exists 0. split; [ reflexivity | apply counter_out; right; left; split; [ exact HN | reflexivity ] ].
Qed.

(** Every state below [N] is reached from [0]. *)
Theorem counter_all_reached (N : nat) :
  triple (@aspStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => s = 0) (fun r => exists k, k < N /\ r = Some (tt, k)).
Proof.
  intros r [k [Hk ->]]. apply (proj2 (aspStExc_read _ (fun s => s = 0) _)).
  exists 0. split; [ reflexivity |]. apply counter_out. left.
  exists k. split; [ lia | split; [ left; exact Hk | reflexivity ] ].
Qed.

(** Paths can be dropped: state [N - 1] alone is reached, by O'Hearn's
    rule of consequence from [counter_all_reached]. *)
Theorem counter_drop_paths (N : nat) :
  0 < N ->
  triple (@aspStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => s = 0) (fun r => r = Some (tt, N - 1)).
Proof.
  intro HN.
  assert (Hpost : forall r, r = Some (tt, N - 1) -> exists k, k < N /\ r = Some (tt, k))
    by (intros r Hr; exists (N - 1); split; [ lia | exact Hr ]).
  exact (first_imp_symmetry_rule_aspStExc nat unit (@denoteStExc _ _ nat unit (counter N)) _ _ _ _
           (conj (counter_all_reached N) (conj (fun s Hs => Hs) Hpost))).
Qed.

(** The bug refutes the correctness triple "from [0], no run raises", both
    as an SP triple and as a Hoare (partial-correctness WP) triple:
    O'Hearn's principle of denial. *)
Theorem counter_not_correct (N : nat) :
  0 < N ->
  ~ triple (@aspStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Over
      (fun s => s = 0) (fun r => r <> None).
Proof.
  intro HN.
  refine (principle_of_denial_aspStExc nat unit (@denoteStExc _ _ nat unit (counter N))
            (fun s => s = 0) (fun r => r = None) _ _
            (conj (counter_bug_reachable N HN) (conj (fun s Hs => Hs) _))).
  intro H. exact (H None eq_refl eq_refl).
Qed.

Theorem counter_not_partially_correct (N : nat) :
  0 < N ->
  ~ triple (@dwlpStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
      (fun s => s = 0) (fun r => r <> None).
Proof.
  intro HN.
  refine (principle_of_denial_dwlpStExc nat unit (@denoteStExc _ _ nat unit (counter N))
            (fun s => s = 0) (fun r => r = None) _ _
            (conj (counter_bug_reachable N HN) (conj (fun s Hs => Hs) _))).
  intro H. exact (H None eq_refl eq_refl).
Qed.

(* ================================================================= *)
(** * Incorrectness logic and Lisbon logic                            *)
(* ================================================================= *)

(** Incorrectness logic: the bug is reached from some start state. *)
Theorem counter_il_any_start (N : nat) :
  0 < N ->
  triple (@aspStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun _ => True) (fun r => r = None).
Proof.
  intros HN r ->. apply (proj2 (aspStExc_read _ (fun _ => True) _)).
  exists 0. split; [ exact I | apply counter_out; right; left; split; [ exact HN | reflexivity ] ].
Qed.

(** Lisbon logic asks the bug to be reachable from every start state: it
    fails from [N], which never raises. *)
Theorem counter_lisbon_fails (N : nat) :
  ~ triple (@awpStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
      (fun _ => True) (fun r => r = None).
Proof.
  intro H. specialize (H N I).
  destruct (proj1 (awpStExc_read _ N _) H) as [o [Ho Hq]].
  apply counter_out in Ho.
  destruct Ho as [[k [_ [_ ->]]] | [[Hlt _] | [_ ->]]]; [ discriminate Hq | lia | exact Hq ].
Qed.

(** It holds from every start state below [N]. *)
Theorem counter_lisbon_below (N : nat) :
  triple (@awpStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => s < N) (fun r => r = None).
Proof.
  intros s Hs. apply (proj2 (awpStExc_read _ s _)).
  exists (Some None). split; [ apply counter_out; right; left; split; [ exact Hs | reflexivity ] | reflexivity ].
Qed.

(* ================================================================= *)
(** * The correctness side                                            *)
(* ================================================================= *)

(** Below [N] every run terminates, raising or stopping below [N]. *)
Theorem counter_dwp_below (N : nat) :
  triple (@dwpStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => s < N) (fun r => r = None \/ exists k, k < N /\ r = Some (tt, k)).
Proof.
  intros s Hs. apply (proj2 (dwpStExc_read _ s _)). intros o Ho.
  apply counter_out in Ho.
  destruct Ho as [[k [_ [Hk ->]]] | [[_ ->] | [Hge _]]].
  - right. exists k. split; [ lia | reflexivity ].
  - left. reflexivity.
  - lia.
Qed.

(** From [N] on, some run runs forever ... *)
Theorem counter_awlp_diverges (N : nat) :
  triple (@awlpStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => N <= s) (fun _ => False).
Proof.
  intros s Hs. apply (proj2 (awlpStExc_read _ s _)).
  exists None. split; [ apply counter_out; right; right; split; [ exact Hs | reflexivity ] | exact I ].
Qed.

(** ... and no run raises: partial correctness holds there. *)
Theorem counter_no_bug_above (N : nat) :
  triple (@dwlpStExc nat ∘ₘₘ @denoteStExc _ _ nat) (counter N) Under
    (fun s => N <= s) (fun r => r <> None).
Proof.
  intros s Hs. apply (proj2 (dwlpStExc_read _ s _)). intros o Ho.
  apply counter_out in Ho.
  destruct Ho as [[k [_ [_ ->]]] | [[Hlt _] | [_ ->]]]; [ discriminate | lia | exact I ].
Qed.
