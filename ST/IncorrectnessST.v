From ExtLib Require Import Monad MonadState StateMonad.
From Incorrectness.ST Require Import SpecST HoareST STExamples.
From Hammer Require Import Hammer Tactics.

Definition Incorrectness {S R}
  (P : S -> Prop)
  (m : state S R)
  (Q : R -> S -> Prop) : Prop :=
  forall p r s',
    Q r s' -> p r s' ->
    exists s, P s /\ uncurry p (runState m s).

Notation "[[ P ]] m [[ Q ]]" := (Incorrectness P m Q) (at level 45).

Hint Unfold Incorrectness conj2 uncurry : incorrectness.
  
Section Incorrectness.

  Variable S : Type.

  Lemma strengthen_pre {A} (m : state S A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop),
      [[ P  ]] m [[ Q ]] ->
      (forall i, P i -> P' i) ->
      [[ P' ]] m [[ Q ]].
  Proof. hauto lq: on unfold: Incorrectness. Qed.

  Lemma strengthen_post {A} (m : state S A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop),
      [[ P ]]  m [[ Q  ]] ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]].
  Proof. sfirstorder. Qed.

  Hint Resolve strengthen_pre strengthen_post : incorrectness.

  Lemma strength_both {A} (m : state S A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop),
      [[ P' ]] m [[ Q  ]] ->
      (forall i, P' i -> P i) ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]].
  Proof. sauto db:incorrectness. Qed.

  Theorem incorrectness_disj_elim : forall R P Q1 Q2 (m : state S R),
      [[ P ]] m [[ disj2 Q1 Q2 ]] ->
      [[ P ]] m [[ Q1 ]] /\ [[ P ]] m [[ Q2 ]].
  Proof. sfirstorder. Qed.
  
  Theorem incorrectness_disj_intro : forall R P Q1 Q2 (m : state S R),
      [[ P ]] m [[ Q1 ]] /\ [[ P ]] m [[ Q2 ]] ->
        [[ P ]] m [[ disj2 Q1 Q2 ]].
  Proof. sfirstorder. Qed.

  (* Agreement and deniable seem not provale under abstract m. *)

End Incorrectness.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST : specst.

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
