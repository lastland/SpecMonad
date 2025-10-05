From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness.Common Require Import Notations StateSpecMonads.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Program Definition obs (S A : Type) (m : state S A) : Pred S A :=
  fun s0 r s1 => runState m s0 = (r, s1).

Program Definition Verify {S A}
  (w : Pred S A) (m : state S A)
  (obs: forall {A}, state S A -> Pred S A) : Prop :=
  ordPred (obs m) w.

Program Definition Correct {S A}
    (pre : S -> Prop)
    (post: S -> A -> S -> Prop)
    (w : Pred S A) : Prop :=
    ordPred w (pp2p (pre,post)). 

Program Definition Incorrect {S A}
  (presumes : S -> Prop)
  (* [achieves] works if does not talk about the initial state *)
  (achieves: A -> S -> Prop) 
  (w : Pred S A) : Prop :=
  forall r s1,
    achieves r s1 ->
    exists s0, w s0 r s1 /\ presumes s0.

Module ReasoningRulesIncorrectness.
  Theorem weaken_pre :
    forall {S A} P P' Q (m : Pred S A),
      Incorrect P Q m ->
      (forall (s : S), P s -> P' s) ->
      Incorrect P' Q m.
  Proof.
    cbv. sauto q: on.
  Qed.

  Theorem strengthen_post :
    forall {S A} P Q Q' (m : Pred S A),
      Incorrect P Q m ->
      (forall r (s : S), Q' r s -> Q r s) ->
      Incorrect P Q' m.
  Proof.
    cbv. sfirstorder.
  Qed.

  Theorem post_disj_intro :
    forall {S A} P Q1 Q2 (m : Pred S A),
    Incorrect P Q1 m ->
    Incorrect P Q2 m ->
    Incorrect P (fun r s => Q1 r s \/ Q2 r s) m.
  Proof.
    cbv. sfirstorder.
  Qed.

  Theorem post_disj_elim :
    forall {S A} P Q1 Q2 (m : Pred S A),
    Incorrect P (fun r s => Q1 r s \/ Q2 r s) m ->
    Incorrect P Q1 m /\
    Incorrect P Q2 m.
  Proof. cbv. sfirstorder. Qed.
End ReasoningRulesIncorrectness.

Module ReasoningRulesCorrectness.
  Theorem strengthen_pre :
    forall {S A} P P' Q (m : Pred S A),
      Correct P Q m ->
      (ordPre P' P) ->
      Correct P' Q m.
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post :
    forall {S A} P Q Q' (m : Pred S A),
      Correct P Q m ->
      (forall s0 r s1, Q s0 r s1 -> Q' s0 r s1) ->
      Correct P Q' m.
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro :
    forall {S A} P Q1 Q2 (m : Pred S A),
    Correct P Q1 m ->
    Correct P Q2 m ->
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m.
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim :
    forall {S A} P Q1 Q2 (m : Pred S A),
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m ->
    Correct P Q1 m /\
    Correct P Q2 m.
  Proof. cbv. sfirstorder. Qed.
End ReasoningRulesCorrectness.

Module ReasoningRulesAgreement.
  Theorem agreement :
    forall {S A} (m : Pred S A) u u' o o',
      Incorrect u u' m ->
      (forall s0, u s0 -> o s0) ->
      Correct o o' m ->
      (forall r s1, u' r s1 -> (exists s0, o' s0 r s1)).
  Proof.
    cbv. intros.

    assert (Incorrect o u' m). {
      apply (ReasoningRulesIncorrectness.weaken_pre _ H H0).
    }
    clear H. clear H0.
    unfold Incorrect in H3.
    specialize H3 with r s1.
    apply H3 in H2. clear H3.
    destruct H2 as [s0 [Hpre H0]].
    exists s0.
    specialize H1 with s0 r s1.
    sauto q: on.    
  Qed.

  Theorem denial :
    forall {S A} (m : Pred S A) u u' o o',
      (Incorrect u u' m /\
       (forall s0, u s0 -> o s0) /\
       ~(forall r s1, u' r s1 -> (exists s0, o' s0 r s1))) ->
      ~(Correct o o' m).
  Proof.
    unfold not.
    intros.
    destruct H as [H1 [H2 H3]].
    apply H3.
    apply (agreement H1 H2 H0).
  Qed.
End ReasoningRulesAgreement.

Module OHearnExample.
  Definition example_3_1_pred : Pred (nat * nat * nat) unit :=
    '(x, y, z) <- get ;;
      if Nat.even x then
        if negb (Nat.even y) then put (x, y, 42) else ret tt
      else ret tt.

  Example example_3_1_incorrect :
    Incorrect
      (fun '(x, y, z) => z = 11)
      (fun _ '(x, y, z) => z = 42 /\
                          Nat.even x = true /\
                          negb (Nat.even y) = true)
      example_3_1_pred.
  Proof.
    cbv. intros.
    destruct s1 as [[x y] z].
    exists (x, y, 11). split; auto; intros. (* surprise, predicates work better than SPosts. *)
    (** The goal looks like: exists a s', (a = (x, y, 11) /\ s' = (x, y, 11)) /\ ...
      and it seems a tactic can easily infer `a` and `s'`.
      
      With SPost, the goal looks like: exists a s', sp _ (a = (x, y, 11) /\ s' = (x, y, 11) _ _)*)
    hauto lq: on drew: off.
  Qed.

  Example example_3_1_incorrect' :
    Incorrect
      (fun '(x, y, z) => True)
      (fun _ '(x, y, z) => z = 42)
      example_3_1_pred.
  Proof.
    unfold Incorrect, ordPred, pp2p, ordPost, example_3_1_pred.
    simpl.
    unfold retPred, bindPred, getPred, putPred.
    destruct r.
    destruct s1 as [[x y] z].
    exists (x, y, z). split; auto; intros.
    exists (x, y, z). exists (x, y, z).
    hauto lq: on drew: off.
  Qed.

  Example example_3_1_correct :
    Correct
      (fun '(x, y, z) => Nat.even x = true /\ negb (Nat.even y) = true)
      (fun _ _ '(x, y, z) => z = 42)
      example_3_1_pred.
  Proof.
    unfold Correct, ordPred, pp2p, ordPost. simpl.
    intros.
    destruct s0 as [[x'' y''] z''].
    destruct s1 as [[x''' y'''] z'''].
    destruct H as [[[x y] z]]. destruct H as [[[x' y'] z']].
    destruct a.
    destruct (Nat.even x) as [] eqn:Eqx;
    destruct (negb (Nat.even y)) as [] eqn:Eqy;
    sfirstorder.
  Qed.

  Example example_3_1_incorrect_unprovable : 
    Incorrect
      (fun '(x, y, z) => z = 11)
      (fun _ '(x, y, z) => z = 42)
      example_3_1_pred.
  Proof.
    cbn. unfold bindPred. unfold getPred. unfold retPred. unfold putPred.
      unfold Incorrect. intros.
    (* This does not seem very automatic; can an SMT solver work here? *)
    destruct s1 as [[x y] z]. destruct r.
    exists (x, y, 11). split; auto; intros. exists (x, y, 11). exists (x, y, 11).
    destruct (Nat.even x); 
    destruct (Nat.even y); 
    split; cbv; eauto; split; eauto; rewrite H.
  Abort. (** this is intentional *)
End OHearnExample.

Module AssertTest.
  Program Definition assertPred {S} (P:Prop) : Pred S P :=
    fun s0 _ s1 => s0 = s1.

  Lemma correct_assert {S} (P:Prop) :
    Correct (fun _ => P) (fun _ _ _ => True) (@assertPred S P).
  Proof. cbv. intros. trivial. Qed.

  Example example_3_1_assert : Pred (nat * nat * nat) unit :=
  '(x, y, z) <- get ;;
  _ <- @assertPred (nat * nat * nat) (Nat.even x = true);;
  _ <- @assertPred (nat * nat * nat) (negb (Nat.even y) = true);;
  put (x, y, 42).
  (* if Nat.even x then
    if negb (Nat.even y) then put (x, y, 42) else ret tt
  else ret tt. *)

  Example example_3_1_correct :
    Correct
      (fun '(x, y, z) => True) (** This is so weird. Why does it accept True here?*)
      (fun _ _ '(x, y, z) => z = 42)
      example_3_1_assert.
  Proof.
    unfold Correct, example_3_1_assert. simpl.
    unfold assertPred, bindPred, retPred, putPred, getPred.
    unfold ordPred, pp2p, ordPost. simpl.
    intros.
    destruct s0 as [[x'' y''] z''].
    destruct s1 as [[x''' y'''] z'''].
    destruct H as [[[x y] z]]. destruct H as [[[x' y'] z']].
    destruct a.
    destruct H.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    destruct H1.
    sfirstorder.
  Qed.

  Example example_3_1_incorrect :
    Incorrect
      (fun '(x, y, z) => z = 11)
      (fun _ '(x, y, z) => z = 42 /\ 
                          (Nat.even x) = true /\
                          negb (Nat.even y) = true)
      example_3_1_assert.
  Proof.
    unfold Incorrect, ordPred, pp2p, ordPost, example_3_1_assert.
    simpl.
    unfold retPred, bindPred, getPred, putPred, assertPred.
    intros.
    destruct r.
    destruct s1 as [[x y] z].
    exists (x, y, 11). 
    hauto lq: on drew: off.
  Qed.

  (** one cannot achieve the post-state z = 42 without also
      depending on (Nat.even x) = true /\ negb (Nat.even y) = true *)
  Example example_3_1_incorrect' :
    Incorrect
      (fun '(x, y, z) => True)
      (fun _ '(x, y, z) => z = 42)
      example_3_1_assert.
  Proof.
    unfold Incorrect, ordPred, pp2p, ordPost, example_3_1_assert.
    simpl.
    unfold retPred, bindPred, getPred, putPred, assertPred.
    intros.
    destruct r.
    destruct s1 as [[x y] z].
    exists (x, y, z). split; eauto.
    exists (x, y, z). exists (x, y, z).
    split; eauto. eexists. 
    + admit. (** Goal: Nat.even x = true *)
    + exists (x, y, z).
      split; eauto. eexists.
      ++ admit. (** Goal: negb (Nat.even y) = true *)
      ++ exists (x, y, z). sfirstorder.
  Abort.
End AssertTest.
