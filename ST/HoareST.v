From ExtLib Require Import Monad MonadState StateMonad.
From Incorrectness Require Import ST.SpecST ST.STExamples.
From Hammer Require Import Hammer Tactics.


Definition Verify {S R} (w : SpecST S R) (m : state S R) : Prop :=
   forall p s, w p s -> uncurry p (runState m s).

Section Verify.

  Variables R S : Type.

  Theorem Verify_ret :
    forall r, @Verify S R (ret r) (ret r).
  Proof. sfirstorder. Qed.

  Theorem Verify_bind :
    forall {A} (m : SpecST S A) m' k k',
      Verify m m' ->
      (forall x, Verify (k x) (k' x)) ->
      @Verify S R (bind m k) (bind m' k').
  Proof.
    cbn. unfold bindST; cbn. intros A m m' k k' H H0.
    intros p s Hm. cbn. unfold Verify in *.
    hauto lq: on drew: off.
  Qed.

  Theorem Verify_get :
    @Verify S S get get.
  Proof. sfirstorder. Qed.

  Theorem Verify_put :
    forall s, @Verify S unit (put s) (put s).
  Proof. sfirstorder. Qed.

End Verify.

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

  Theorem read_inc_write_hoare :
    {{ fun s => s >= 10 }} read_inc_write {{ fun _ s => s >= 11 }}.
  Proof.
    intros. unfold read_inc_write. cbn.
    autounfold with specst.
    intros p s Hs Hp.
    apply Hp. lia.
  Qed.

  Theorem read_inc_write_spec' :
    Verify read_inc_write_spec read_inc_write.
  Proof.
    intros p s Hs.
    unfold read_inc_write. unfold read_inc_write_spec in Hs.
    cbn in *. unfold putST in Hs. assumption.
  Qed.
End Examples.
