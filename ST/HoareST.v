From ExtLib Require Import Monad MonadState StateMonad.
From Incorrectness Require Import ST.SpecST ST.STExamples.
From Hammer Require Import Hammer Tactics.

Definition Hoare {S R} (P : S -> Prop) (m : state S R) (Q : R -> S -> Prop) : Prop :=
  forall p s, P s -> (forall r s', Q r s' -> p r s') -> uncurry p (runState m s).

Notation "{{ P }} m {{ Q }}" := (Hoare P m Q) (at level 45).

Hint Unfold Hoare conj2 uncurry : hoare.
  
Section Hoare.

  Variable S : Type.

  Lemma relax_pre {A} (m :state S A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop),
      {{ P' }} m {{ Q }} ->
      (forall i, P i -> P' i) ->
      {{ P  }} m {{ Q }}.
  Proof. sfirstorder. Qed.

  Lemma relax_post {A} (m : state S A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop),
      {{ P }} m {{ Q  }} ->
      (forall a s, Q a s -> Q' a s) ->
      {{ P }} m {{ Q' }}.
  Proof. sfirstorder. Qed.

  Lemma relax_both {A} (m : state S A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop),
      {{ P' }} m {{ Q  }} ->
      (forall i, P i -> P' i) ->
      (forall a s, Q a s -> Q' a s) ->
      {{ P }} m {{ Q' }}.
  Proof.
    intros. eapply relax_pre; [ eapply relax_post | ].
    all: eassumption.
  Qed.

  Theorem hoare_conj_elim : forall R P Q1 Q2 (m : state S R),
      {{ P }} m {{ conj2 Q1 Q2 }} ->
      {{ P }} m {{ Q1 }} /\ {{ P }} m {{ Q2 }}.
  Proof. sfirstorder. Qed.
  
  Theorem hoare_conj_intro : forall R P Q1 Q2 (m : state S R),
      {{ P }} m {{ Q1 }} /\ {{ P }} m {{ Q2 }} ->
        {{ P }} m {{ conj2 Q1 Q2 }}.
  Proof.
    intros R P Q1 Q2 m [HQ1 HQ2]. 
    autounfold with hoare in *; simpl in *.
    fcrush.
  Qed.

End Hoare.

From Coq Require Import Nat Lia PeanoNat.

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST : specst.

  Theorem read_inc_write_spec :
    {{ fun s => s >= 10 }} read_inc_write {{ fun _ s => s >= 11 }}.
  Proof.
    intros. unfold read_inc_write. cbn.
    autounfold with specst.
    intros p s Hs Hp.
    apply Hp. lia.
  Qed.

End Examples.
