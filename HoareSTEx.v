From ExtLib Require Import Monad MonadState.
From Spec Require Import SpecSTEx.
From Hammer Require Import Hammer Tactics.

(* Technically, [m] should be an ordinary monad that can be morphed to a
  specification monad, but we directly use specification monads here for
  simplicity. *)
Definition Hoare {S R E}
  (P : S -> Prop) (m : SpecSTEx S E R) (Q : R -> S -> Prop) (H : E -> S -> Prop) : Prop :=
  forall p h s,
    P s ->
    (forall r s', Q r s' -> p r s') ->
    (forall e s', H e s' -> h e s') ->
    m p h s.

Notation "{{ P }} m {{ Q }} {{ H }}" := (Hoare P m Q H) (at level 45).

Hint Unfold Hoare conj2 : hoare.
  
Section Hoare.

  Variable S E : Type.

  Lemma relax_pre {A} (m : SpecSTEx S E A) :
    forall (P P' : S -> Prop) (Q : A -> S -> Prop) (H : E -> S -> Prop),
      {{ P' }} m {{ Q }} {{ H }} ->
      (forall i, P i -> P' i) ->
      {{ P  }} m {{ Q }} {{ H }}.
  Proof. sfirstorder. Qed.

  Lemma relax_post {A} (m : SpecSTEx S E A) :
    forall (P : S -> Prop) (Q Q' : A -> S -> Prop) (H : E -> S -> Prop),
      {{ P }} m {{ Q  }} {{ H }} ->
      (forall a s, Q a s -> Q' a s) ->
      {{ P }} m {{ Q' }} {{ H }}.
  Proof. sfirstorder. Qed.

  Lemma relax_both {A} (m : SpecSTEx S E A) :
    forall (P P' : S -> Prop) (Q Q' : A -> S -> Prop) (H : E -> S -> Prop),
      {{ P' }} m {{ Q  }} {{ H }} ->
      (forall i, P i -> P' i) ->
      (forall a s, Q a s -> Q' a s) ->
      {{ P }} m {{ Q' }} {{ H }}.
  Proof.
    intros. eapply relax_pre; [ eapply relax_post | ].
    all: eassumption.
  Qed.

  Theorem hoare_conj_elim : forall R P Q1 Q2 H (m : SpecSTEx S E R),
      {{ P }} m {{ conj2 Q1 Q2 }} {{ H }} ->
      {{ P }} m {{ Q1 }} {{ H }} /\ {{ P }} m {{ Q2 }} {{ H }}.
  Proof.
    intros R P Q1 Q2 H m H0.
    autounfold with hoare in *. hauto lq: on.
  Qed.
  
  (* This seems not provable. *)
  Theorem hoare_conj_intro : forall R P Q1 Q2 H (m : SpecSTEx S E R),
      {{ P }} m {{ Q1 }} {{ H }} /\ {{ P }} m {{ Q2 }} {{ H }} ->
        {{ P }} m {{ conj2 Q1 Q2 }} {{ H }}.
  Proof.
    intros R P Q1 Q2 H m [HQ1 HQ2]. 
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

  Definition read_inc_write : SpecSTEx nat unit unit :=
    x <- get ;; put (x + 1).

  Theorem read_inc_write_spec {H} :
    {{ fun s => s >= 10 }} read_inc_write {{ fun _ s => s >= 11 }} {{ H }}.
  Proof.
    intros. unfold read_inc_write. cbn.
    autounfold with specst.
    intros p h s n Hp Hh.
    apply Hp. lia.
  Qed.

End Examples.
