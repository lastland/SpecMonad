From ExtLib Require Import Monad MonadState.
From Spec Require Import SpecST.
From Hammer Require Import Hammer Tactics.

(* Technically, [m] should be an ordinary monad that can be morphed to a
  specification monad, but we directly use specification monads here for
  simplicity. *)
Definition Hoare {S R} (P : S -> Prop) (m : SpecST S R) (Q : R -> S -> Prop) : Prop :=
  forall p s, P s -> (forall r s', Q r s' -> p r s') -> m p s.

Notation "{{ P }} m {{ Q }}" := (Hoare P m Q) (at level 45).

Hint Unfold Hoare conj2 : hoare.
  
Section Hoare.

  Variable S : Type.

  Lemma relax_pre {A} (m : SpecST S A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop),
      {{ P' }} m {{ Q }} ->
      (forall i, P i -> P' i) ->
      {{ P  }} m {{ Q }}.
  Proof.
    intros P P' Q Hm Hrelax p i HP HQ.
    apply Hm; sfirstorder.
  Qed.

  Lemma relax_post {A} (m : SpecST S A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop),
      {{ P }} m {{ Q  }} ->
      (forall a s, Q a s -> Q' a s) ->
      {{ P }} m {{ Q' }}.
  Proof.
    intros P Q Q' Hm Hrelax p ib HP HQ. 
    apply Hm; firstorder.
  Qed.

  Lemma relax_both {A} (m : SpecST S A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop),
      {{ P' }} m {{ Q  }} ->
      (forall i, P i -> P' i) ->
      (forall a s, Q a s -> Q' a s) ->
      {{ P }} m {{ Q' }}.
  Proof.
    intros. eapply relax_pre; [ eapply relax_post | ].
    all: eassumption.
  Qed.

  Theorem hoare_conj_elim : forall R P Q1 Q2 (m : SpecST S R),
      {{ P }} m {{ conj2 Q1 Q2 }} ->
      {{ P }} m {{ Q1 }} /\ {{ P }} m {{ Q2 }}.
  Proof. sfirstorder. Qed.

  
  (* This seems not provable. *)
  Theorem hoare_conj_intro : forall R P Q1 Q2 (m : SpecST S R),
      {{ P }} m {{ Q1 }} /\ {{ P }} m {{ Q2 }} ->
        {{ P }} m {{ conj2 Q1 Q2 }}.
  Proof.
    intros R P Q1 Q2 m [HQ1 HQ2]. 
    autounfold with hoare in *; simpl in *.
    intros p s HP Hconj.
    specialize (HQ1 Q1 s HP ltac:(auto)).
    specialize (HQ2 Q2 s HP ltac:(auto)).
  Abort.

End Hoare.

From Coq Require Import Nat Lia PeanoNat.

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST : specst.

  Definition read_inc_write : SpecST nat unit :=
    x <- get ;; put (x + 1).

  Theorem read_inc_write_spec :
    {{ fun s => s >= 10 }} read_inc_write {{ fun _ s => s >= 11 }}.
  Proof.
    intros. unfold read_inc_write. cbn.
    autounfold with specst.
    intros p s Hs Hp.
    apply Hp. lia.
  Qed.

End Examples.
