From ExtLib Require Import Monad MonadState.
From Spec Require Import SpecST.
From Hammer Require Import Hammer Tactics.

Section Incorrectness.

  Variable S : Type.

  Definition Incorrectness {R} (P : S -> Prop) (m : SpecST S R) (Q : R -> S -> Prop) : Prop :=
    forall p, exists s, P s /\ (forall r s', Q r s' -> p r s') /\ m p s.

  Notation "[[ P ]] m [[ Q ]]" := (Incorrectness P m Q) (at level 45).

  Hint Unfold Incorrectness conj2 : incorrectness.
  
  Lemma strengthen_pre {A} (m : SpecST S A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop),
      [[ P' ]] m [[ Q ]] ->
      (forall i, P' i -> P i) ->
      [[ P  ]] m [[ Q ]].
  Proof. sfirstorder. Qed.

  Lemma strengthen_post {A} (m : SpecST S A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop),
      [[ P ]] m [[ Q  ]] ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]].
  Proof. sfirstorder. Qed.

  Hint Resolve strengthen_pre strengthen_post : incorrectness.

  Lemma strength_both {A} (m : SpecST S A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop),
      [[ P' ]] m [[ Q  ]] ->
      (forall i, P' i -> P i) ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]].
  Proof. sauto db:incorrectness. Qed.

  Theorem hoare_conj_elim : forall R P Q1 Q2 (m : SpecST S R),
      [[ P ]] m [[ disj2 Q1 Q2 ]] ->
      [[ P ]] m [[ Q1 ]] /\ [[ P ]] m [[ Q2 ]].
  Proof.
    intros R P Q1 Q2 m H.
    split; intros p; specialize (H p).
    all: sauto lq: on.
  Qed.
  
  Theorem hoare_conj_intro : forall R P Q1 Q2 (m : SpecST S R),
      [[ P ]] m [[ Q1 ]] /\ [[ P ]] m [[ Q2 ]] ->
        [[ P ]] m [[ disj2 Q1 Q2 ]].
  Proof. sfirstorder. Qed.

End Incorrectness.
