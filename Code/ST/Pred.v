From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.

From Coq Require Import Nat Lia PeanoNat RelationClasses.

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Program Definition obs (S A : Type) (m : state S A) : StatePred S A :=
  fun s0 r s1 => runState m s0 = (r, s1).

Program Definition Verify {S A}
  (w : StatePred S A) (m : state S A) : Prop :=
  ordPred (obs m) w.

Program Definition Correct {S A}
    (pre : S -> Prop)
    (post: S -> A -> S -> Prop)
    (m : state S A) : Prop :=
    Verify (pp2p (pre, post)) m. 

Program Definition VerifyIncorrect {S A}
  (presumes : S -> Prop)
  (* [achieves] works if does not talk about the initial state *)
  (achieves: A -> S -> Prop) 
  (w : StatePred S A) : Prop :=
  forall r s1,
    achieves r s1 ->
    exists s0, w s0 r s1 /\ presumes s0.

Program Definition Incorrect {S A}
  (presumes : S -> Prop)
  (achieves: A -> S -> Prop) 
  (m : state S A) : Prop :=
  VerifyIncorrect presumes achieves (obs m).

Module ReasoningRulesIncorrectness.
  Theorem weaken_pre :
    forall {S A} P P' Q (m : StatePred S A),
      VerifyIncorrect P Q m ->
      (forall (s : S), P s -> P' s) ->
      VerifyIncorrect P' Q m.
  Proof.
    cbv. sauto q: on.
  Qed.

  Theorem strengthen_post :
    forall {S A} P Q Q' (m : StatePred S A),
      VerifyIncorrect P Q m ->
      (forall r (s : S), Q' r s -> Q r s) ->
      VerifyIncorrect P Q' m.
  Proof.
    cbv. sfirstorder.
  Qed.

  Theorem post_disj_intro :
    forall {S A} P Q1 Q2 (m : StatePred S A),
    VerifyIncorrect P Q1 m ->
    VerifyIncorrect P Q2 m ->
    VerifyIncorrect P (fun r s => Q1 r s \/ Q2 r s) m.
  Proof.
    cbv. sfirstorder.
  Qed.

  Theorem post_disj_elim :
    forall {S A} P Q1 Q2 (m : StatePred S A),
    VerifyIncorrect P (fun r s => Q1 r s \/ Q2 r s) m ->
    VerifyIncorrect P Q1 m /\
    VerifyIncorrect P Q2 m.
  Proof. cbv. sfirstorder. Qed.
End ReasoningRulesIncorrectness.

Module ReasoningRulesCorrectness.
  Theorem strengthen_pre :
    forall {S A} P P' Q (m : state S A),
      Correct P Q m ->
      (ordPre P' P) ->
      Correct P' Q m.
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post :
    forall {S A} P Q Q' (m : state S A),
      Correct P Q m ->
      (forall s0 r s1, Q s0 r s1 -> Q' s0 r s1) ->
      Correct P Q' m.
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro :
    forall {S A} P Q1 Q2 (m : state S A),
    Correct P Q1 m ->
    Correct P Q2 m ->
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m.
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim :
    forall {S A} P Q1 Q2 (m : state S A),
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m ->
    Correct P Q1 m /\
    Correct P Q2 m.
  Proof. cbv. sfirstorder. Qed.
End ReasoningRulesCorrectness.

Module ReasoningRulesAgreement.
  Theorem agreement :
    forall {S A} (m : state S A) u u' o o',
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
    unfold Incorrect, VerifyIncorrect in H3.
    specialize H3 with r s1.
    apply H3 in H2. clear H3.
    destruct H2 as [s0 [Hpre H0]].
    exists s0.
    specialize H1 with s0 r s1.
    sauto q: on.    
  Qed.

  Theorem denial :
    forall {S A} (m : state S A) u u' o o',
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
  Definition example_3_1_state : state (nat * nat * nat) unit :=
    '(x, y, z) <- get ;;
      if Nat.even x then
        if negb (Nat.even y) then put (x, y, 42) else ret tt
      else ret tt.
  
  (* Definition example_3_1_pred : StatePred (nat * nat * nat) unit :=
    '(x, y, z) <- get ;;
      if Nat.even x then
        if negb (Nat.even y) then put (x, y, 42) else ret tt
      else ret tt. *)

  Example example_3_1_correct :
    Correct
      (fun '(x, y, z) => Nat.even x = true /\ negb (Nat.even y) = true)
      (fun _ _ '(x, y, z) => z = 42)
      example_3_1_state.
  Proof.
    unfold Correct, Verify, ordPred, pp2p, ordPost. simpl.
    intros.
    destruct s0 as [[x y] z].
    destruct s1 as [[x' y'] z'].
    unfold obs, runState in H. simpl in H.
    destruct H0.
    rewrite H0 in H.
    rewrite H1 in H.
    simpl in H.
    sfirstorder.
  Qed.

  Example example_3_1_incorrect :
    Incorrect
      (fun '(x, y, z) => z = 11)
      (fun _ '(x, y, z) => z = 42 /\
                          Nat.even x = true /\
                          negb (Nat.even y) = true)
      example_3_1_state.
  Proof.
    unfold Incorrect, VerifyIncorrect.
    intros.
    destruct r.
    destruct s1 as [[x y] z].
    destruct H as [Hz [Hx Hy]].
    exists (x, y, 11).
    split.
    unfold obs, runState, example_3_1_state. simpl.
    + rewrite Hx. rewrite Hy. rewrite Hz. simpl. reflexivity. 
    + reflexivity.
  Qed.

  Example example_3_1_incorrect' :
    Incorrect
      (fun '(x, y, z) => True)
      (fun _ '(x, y, z) => z = 42)
      example_3_1_state.
  Proof.
    unfold Incorrect, VerifyIncorrect, ordPred, pp2p, ordPost, example_3_1_state, obs.
    simpl.
    destruct r.
    destruct s1 as [[x y] z].
    exists (x, y, z).
    split; auto; intros.
    unfold runState.
    destruct (Nat.even x);
    destruct (negb (Nat.even y)); sfirstorder.
  Qed.


  Example example_3_1_incorrect_unprovable : 
    Incorrect
      (fun '(x, y, z) => z = 11)
      (fun _ '(x, y, z) => z = 42)
      example_3_1_state.
  Proof.
    unfold Incorrect, VerifyIncorrect, ordPred, pp2p, ordPost, example_3_1_state, obs.
    simpl.
    destruct r.
    destruct s1 as [[x' y'] z'].
    exists (x', y', 11).
    split; auto; intros.
    unfold runState.
    destruct (Nat.even x');
    destruct (negb (Nat.even y')); auto.
    + sfirstorder.
    + admit.
    + admit.
    + admit.  
  Abort. (** this is intentional *)
End OHearnExample.
