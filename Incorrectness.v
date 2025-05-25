From ExtLib Require Import Monad MonadState.
From Spec Require Import SpecST.
From Hammer Require Import Hammer Tactics.

Definition Incorrectness {S R} (P : S -> Prop) (m : SpecST S R) (Q : R -> S -> Prop) : Prop :=
  forall p r s', Q r s' -> p r s' -> exists s, P s /\ m p s.

Notation "[[ P ]] m [[ Q ]]" := (Incorrectness P m Q) (at level 45).

Hint Unfold Incorrectness conj2 : incorrectness.
  
Section Incorrectness.

  Variable S : Type.

  Lemma strengthen_pre {A} (m : SpecST S A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop),
      [[ P' ]] m [[ Q ]] ->
      (forall i, P' i -> P i) ->
      [[ P  ]] m [[ Q ]].
  Proof.
    intros P P' Q H H0 p r s Hp. 
    specialize (H p r s Hp).
    sfirstorder.
  Qed.

  Lemma strengthen_post {A} (m : SpecST S A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop),
      [[ P ]] m [[ Q  ]] ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]].
  Proof.
    intros P Q Q' H H0 p r s Hp.
    specialize (H p r s ltac:(auto)).
    sfirstorder.
  Qed.

  Hint Resolve strengthen_pre strengthen_post : incorrectness.

  Lemma strength_both {A} (m : SpecST S A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop),
      [[ P' ]] m [[ Q  ]] ->
      (forall i, P' i -> P i) ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]].
  Proof. sauto db:incorrectness. Qed.

  Theorem incorrectness_disj_elim : forall R P Q1 Q2 (m : SpecST S R),
      [[ P ]] m [[ disj2 Q1 Q2 ]] ->
      [[ P ]] m [[ Q1 ]] /\ [[ P ]] m [[ Q2 ]].
  Proof.
    intros R P Q1 Q2 m H.
    split; intros p; specialize (H p).
    all: sauto lq: on.
  Qed.
  
  Theorem incorrectness_disj_intro : forall R P Q1 Q2 (m : SpecST S R),
      [[ P ]] m [[ Q1 ]] /\ [[ P ]] m [[ Q2 ]] ->
        [[ P ]] m [[ disj2 Q1 Q2 ]].
  Proof. sfirstorder. Qed.

End Incorrectness.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST : specst.

  Definition read_inc_write : SpecST nat unit :=
    x <- get ;; put (x + 1).

  Theorem read_inc_write_spec :
    [[ fun s => s >= 10 ]] read_inc_write [[ fun _ s => s >= 11 ]].
  Proof.
    intros. unfold read_inc_write.
    cbn. autounfold with specst.
    intros p [] s' Hs' Hp.
    exists (s' - 1). split; [lia |].
    destruct s'; [lia |].
    scongruence use: Nat.sub_0_r, Nat.add_1_r.
  Qed.

  Definition read_if_inc_write : SpecST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Theorem read_if_inc_write_spec :
    [[ fun s => s >= 42 ]] read_if_inc_write [[ fun _ s => s > 42 ]].
  Proof.
    intros. unfold read_if_inc_write.
    intros p [] s' Hs' Hp.
    exists (s' - 1). split; [lia |].
    cbn. autounfold with specst.
    cbn. pose proof (Nat.leb_spec0 42 (s' - 1)) as Hs.
    inversion Hs; simpl; [| lia].
    destruct s'; [lia |].
    scongruence use: Nat.sub_0_r, Nat.add_1_r.
  Qed.
End Examples.
