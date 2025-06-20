From ExtLib Require Import Monad MonadState.
From Incorrectness.ST Require Import SpecSTEx HoareSTEx.
From Hammer Require Import Hammer Tactics.

Definition Incorrectness {S E R}
  (P : S -> Prop)
  (m : SpecSTEx S E R)
  (Q : R -> S -> Prop)
  (H : E -> S -> Prop) : Prop :=
  forall p h r e s',
    Q r s' -> p r s' ->
    H e s' -> h e s' -> 
    exists s, P s /\ m p h s.

Notation "[[ P ]] m [[ Q ]] [[ H ]]" := (Incorrectness P m Q H) (at level 45).

Hint Unfold Incorrectness conj2 disj2 : incorrectness.
  
Section Incorrectness.

  Variable S E : Type.

  Lemma strengthen_pre {A} (m : SpecSTEx S E A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop) H,
      [[ P' ]] m [[ Q ]] [[ H ]] ->
      (forall i, P' i -> P i) ->
      [[ P  ]] m [[ Q ]] [[ H ]].
  Proof. 
    intros P P' Q ? Hm ? p h r e s ? ? ? ?.
    specialize (Hm p h r e s).
    sfirstorder.
  Qed.

  Lemma strengthen_post {A} (m : SpecSTEx S E A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop) H,
      [[ P ]] m [[ Q  ]] [[ H ]] ->
      (forall a s, Q' a s -> Q a s) ->
      [[ P ]] m [[ Q' ]] [[ H ]].
  Proof.
    intros P P' Q ? Hm ? p h r e s ? ? ? ?.
    specialize (Hm p h r e s ltac:(auto)).
    sfirstorder.
  Qed.

  Lemma strengthen_exc {A} (m : SpecSTEx S E A) :
    forall (P : S -> Prop) (Q : A -> S -> Prop) H H',
      [[ P ]] m [[ Q ]] [[ H  ]] ->
      (forall a s, H' a s -> H a s) ->
      [[ P ]] m [[ Q ]] [[ H' ]].
  Proof.
    intros P P' Q ? Hm ? p h r e s ? ? ? ?.
    specialize (Hm p h r e s ltac:(auto)).
    sfirstorder.
  Qed.

  Hint Resolve strengthen_pre strengthen_post strengthen_exc : incorrectness.

  Lemma strength_all {A} (m : SpecSTEx S E A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop) H H',
      [[ P' ]] m [[ Q  ]] [[ H  ]] ->
      (forall i, P' i -> P i) ->
      (forall a s, Q' a s -> Q a s) ->
      (forall a s, H' a s -> H a s) ->
      [[ P  ]] m [[ Q' ]] [[ H' ]].
  Proof. sauto db:incorrectness. Qed.

  Theorem incorrectness_disj_elim :
    forall R P Q1 Q2 H1 H2 (m : SpecSTEx S E R),
      [[ P ]] m [[ disj2 Q1 Q2 ]] [[ disj2 H1 H2 ]] ->
      [[ P ]] m [[ Q1 ]] [[ H1 ]] /\ [[ P ]] m [[ Q2 ]] [[ H2 ]].
  Proof.
    intros R P Q1 Q2 H1 H2 m Hm.
    split; intros p; specialize (Hm p).
    all: sauto lq: on.
  Qed.
  
  Theorem incorrectness_disj_intro :
    forall R P Q1 Q2 H (m : SpecSTEx S E R),
      [[ P ]] m [[ Q1 ]] [[ H ]] /\ [[ P ]] m [[ Q2 ]] [[ H ]] ->
        [[ P ]] m [[ disj2 Q1 Q2 ]] [[ H ]].
  Proof. sfirstorder. Qed.

  Theorem incorrectness_disj_intro_exc :
    forall R P Q H1 H2 (m : SpecSTEx S E R),
      [[ P ]] m [[ Q ]] [[ H1 ]] /\ [[ P ]] m [[ Q ]] [[ H2 ]] ->
        [[ P ]] m [[ Q ]] [[ disj2 H1 H2 ]].
  Proof. sfirstorder. Qed.

End Incorrectness.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST : specst.

  Theorem read_inc_write_spec {H} :
    [[ fun s => s >= 10 ]] read_inc_write [[ fun _ s => s >= 11 ]] [[ H ]].
  Proof.
    intros. unfold read_inc_write.
    cbn. autounfold with specst.
    intros p h [] [] s' Hs' Hp HH Hh.
    exists (s' - 1). split; [lia |].
    destruct s'; [lia |].
    scongruence use: Nat.sub_0_r, Nat.add_1_r.
  Qed.

  Theorem read_if_inc_write_spec {H} :
    [[ fun s => s >= 42 ]] read_if_inc_write [[ fun _ s => s > 42 ]] [[ H ]].
  Proof.
    intros. unfold read_if_inc_write.
    intros p h [] [] s' Hs' Hp HH Hh.
    exists (s' - 1). split; [lia |].
    cbn. autounfold with specst.
    cbn. pose proof (Nat.leb_spec0 42 (s' - 1)) as Hs.
    inversion Hs; simpl; [| lia].
    destruct s'; [lia |].
    scongruence use: Nat.sub_0_r, Nat.add_1_r.
  Qed.
End Examples.
