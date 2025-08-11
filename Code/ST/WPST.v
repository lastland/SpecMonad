From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.Examples ST.ST ST.WFST.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition WPST :=
    (A -> S -> Prop) -> (S -> Prop).

  Definition ordWPST (m1 m2 : WPST) : Prop :=
    forall p s0, m1 p s0 -> m2 p s0.

  Definition wp2pp (w : WPST) : (S -> Prop) * (S -> A -> S -> Prop) :=
    (w (fun _ _ => True), fun s0 a s1 => forall p, w p s0 -> p a s1).

  Program Definition wp2sp (w : WPST) : WFST S A :=
    let (pre, post) := wp2pp w in
    pp2sp pre post.

End Types.

Section WPST.

  Variable S : Type.

  Program Definition retWPST {A} (a : A) : WPST S A :=
    fun p s0 => p a s0.

  Program Definition bindWPST {A B}
    (m : WPST S A) (k : A -> WPST S B) : WPST S B :=
    fun p => m (fun a s1 => k a p s1).

  Program Definition getWPST : WPST S S :=
    fun p s0 => p s0 s0.

  Program Definition putWPST (s : S) : WPST S unit :=
    fun p s0 => p tt s.

  #[global] Instance Monad__WPST : Monad (WPST S) :=
    {| ret := fun _ => retWPST ;
       bind := fun _ _ => bindWPST |}.

  #[global] Instance MonadState__WPST : MonadState S (WPST S) :=
    {| get := getWPST ;
       put := putWPST |}.

End WPST.

Hint Unfold getWPST putWPST retWPST bindWPST ordWPST : mst.

Program Definition CorrectWP {R S}
  (pre : S -> Prop)
  (post: S -> R -> S -> Prop)
  (w : WPST S R) : Prop :=
  ordWPST (fun p s0 => pre s0 /\ (forall r s1, post s0 r s1 -> p r s1)) w.

Program Definition IncorrectWP {R S}
  (presumes : S -> Prop)
  (achieves : R -> S -> Prop)
  (w : WPST S R) : Prop :=
  Incorrect' presumes achieves (wp2sp w).

Hint Unfold CorrectWP IncorrectWP wp2sp : mst.

Module Examples.

    Definition example_3_1_WPST : WPST (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else ret tt.

    Theorem example_3_1_incorrect :
      IncorrectWP
        (fun '(x, y, z) => z = 11)
        (fun _ '(x, y, z) => z = 42 /\
                            Nat.even x = true /\
                            negb (Nat.even y) = true)
        example_3_1_WPST.
    Proof.
      unfold IncorrectWP. unfold Incorrect'.
      autounfold with mst. cbn; intros.
      (* This does not seem very automatic; can an SMT solver work here? *)
      destruct s as [[x y] z].
      exists (x, y, 11). split; auto; intros. split. reflexivity.
      unfold getWPST, putWPST, retWPST, bindWPST.
      destruct (Nat.even x); destruct (Nat.even y); destruct r;
      hauto lq: on drew: off.
    Qed.


    Theorem example_3_1_incorrect' : (** should be unprovable *)
      IncorrectWP
        (fun '(x, y, z) => z = 11)
        (fun _ '(x, y, z) => z = 42)
        example_3_1_WPST.
    Proof.
      unfold IncorrectWP. unfold Incorrect'.
      autounfold with mst. cbn; intros.
      (* This does not seem very automatic; can an SMT solver work here? *)
      destruct s as [[x y] z].
      exists (x, y, 11). split; auto; intros. split. reflexivity.
      destruct (Nat.even x); destruct (Nat.even y); destruct r; simpl; intros.
      + rewrite H.
    Abort.

End Examples.


Program Definition TestCorrectWP {R S}
  (pre : S -> Prop)
  (post: S -> R -> S -> Prop)
  (w : WPST S R) : Prop :=
  IncorrectWP pre (fun r s1 => exists s0, pre s0 /\ ~(post s0 r s1)) w.

Hint Unfold TestCorrectWP : mst.

Module TestExamples.

    Theorem example_3_1_correct :
      CorrectWP
        (fun '(x, y, z) => Nat.even x = true /\ negb (Nat.even y) = true)
        (fun _ _ '(x, y, z) => z = 42)
        Examples.example_3_1_WPST.
    Proof.
        unfold Examples.example_3_1_WPST.
        simpl.
        autounfold with mst. cbn; intros.
        destruct s0 as [[x y] z].
        destruct (Nat.even x); destruct (Nat.even y); simpl; intros;
        hauto lq: on drew: off.
    Qed.

End TestExamples.