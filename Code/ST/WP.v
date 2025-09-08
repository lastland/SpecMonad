From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.StateSpecMonads.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Program Definition obs (S A : Type) (m : state S A) : WP S A :=
  fun p s0 => let (r, s1) := runState m s0 in p r s1.

Program Definition Verify {S A}
  (w : WP S A) (m : state S A)
  (obs: forall {A}, state S A -> WP S A) : Prop :=
  ordWP w (obs m). 

Program Definition Correct {S A}
    (pre : S -> Prop)
    (post: S -> A -> S -> Prop)
    (w : WP S A) : Prop :=
    ordWP (pp2wp (pre, post)) w. 

Program Definition Incorrect {S A}
  (presumes : S -> Prop)
  (achieves: A -> S -> Prop) (* [achieves] works if does not talk about the initial state *)
  (w : WP S A) : Prop :=
  forall r s1,
    achieves r s1 ->
    exists s0, (wp2p w) s0 r s1 /\ presumes s0.

Module ReasoningRulesIncorrectness.
  Theorem weaken_pre :
    forall {S A} P P' Q (m : WP S A),
      Incorrect P Q m ->
      (forall (s : S), P s -> P' s) ->
      Incorrect P' Q m.
  Proof.
    cbv. sauto q: on.
  Qed.

  Theorem strengthen_post :
    forall {S A} P Q Q' (m : WP S A),
      Incorrect P Q m ->
      (forall r (s : S), Q' r s -> Q r s) ->
      Incorrect P Q' m.
  Proof.
    cbv. sfirstorder.
  Qed.

  Theorem post_disj_intro :
    forall {S A} P Q1 Q2 (m : WP S A),
    Incorrect P Q1 m ->
    Incorrect P Q2 m ->
    Incorrect P (fun r s => Q1 r s \/ Q2 r s) m.
  Proof.
    cbv. sfirstorder.
  Qed.

  Theorem post_disj_elim :
    forall {S A} P Q1 Q2 (m : WP S A),
    Incorrect P (fun r s => Q1 r s \/ Q2 r s) m ->
    Incorrect P Q1 m /\
    Incorrect P Q2 m.
  Proof.
    cbv.
    sfirstorder.
  Qed.
End ReasoningRulesIncorrectness.

Module ReasoningRulesCorrectness.
  Theorem strengthen_pre :
    forall {S A} P P' Q (m : WP S A),
      Correct P Q m ->
      (forall (s0 : S), P' s0 -> P s0) ->
      Correct P' Q m.
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post :
    forall {S A} P Q Q' (m : WP S A),
      Correct P Q m ->
      (forall s0 r s1, Q s0 r s1 -> Q' s0 r s1) ->
      Correct P Q' m.
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro :
    forall {S A} P Q1 Q2 (m : WP S A),
    Correct P Q1 m ->
    Correct P Q2 m ->
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m.
  Proof.
    unfold Correct.
    unfold ordWP.
    intros.
    specialize H with p s0.
    specialize H0 with p s0.
  Admitted.

  Theorem post_conj_elim :
    forall {S A} P Q1 Q2 (m : WP S A),
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m ->
    Correct P Q1 m /\
    Correct P Q2 m.
  Proof. cbv. sfirstorder. Qed.
End ReasoningRulesCorrectness.

Module ReasoningRulesAgreement.
  Theorem agreement :
    forall {S A} (m : WP S A) u u' o o',
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
    specialize H1 with (fun r s1 => o' s0 r s1) s0.
    simpl in H1.
    cbv in Hpre.
    sauto q: on.    
  Qed.

  Theorem denial :
    forall {S A} (m : WP S A) u u' o o',
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
    Definition example_3_1_WP : WP (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else ret tt.

    Theorem example_3_1_incorrect :
      Incorrect
        (fun '(x, y, z) => z = 11)
        (fun _ '(x, y, z) => z = 42 /\
                            Nat.even x = true /\
                            negb (Nat.even y) = true)
        example_3_1_WP.
    Proof.
      unfold Incorrect. unfold example_3_1_WP. unfold wp2p.
      unfold get. unfold put. unfold wp2pp. unfold pp2p. simpl.
      autounfold with mst. cbn; intros.
      destruct r.
      destruct s1 as [[x y] z].
      destruct H as [Hz [Hx Hy]].
      autounfold with mst.
      exists (x, y, 11). 
      rewrite Hx. rewrite Hy. rewrite Hz.
      simpl.
      sfirstorder.
    Qed.
End OHearnExample.