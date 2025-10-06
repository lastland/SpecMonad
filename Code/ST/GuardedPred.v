From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.StateSpecMonads Common.Guarded.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.


Section GuardedPredState.

  (* Computation monad *)

  Definition M S A :=
    S -> guarded (S * A).

  Instance Monad_M S : Monad (M S) := {|
    ret A x := fun s0 => ret (s0, x);
    bind A B c f := fun s0 => bind (c s0) (fun '(s1, x) => f x s1)
  |}.

  Instance GuardedMonad_M S : @GuardedMonad (M S) (Monad_M S) := {|
    guard p := fun s0 => bind (guard p) (fun h => ret (s0, h))
  |}.

  Definition get' {S} : M S S :=
    fun s0 => ret (s0, s0).

  Definition put' {S} (s : S) : M S unit :=
    fun s0 => ret (s, tt).

  #[global] Instance MonadState__M {S} : MonadState S (M S) :=
    {| get := get' ;
       put := put' |}.    

  (* Effect observation *)

  Definition obsPred {S A} (c : M S A) : Pred S A :=
    fun s0 r s1 =>
      forall proof, (projT2 (c s0) proof) = (s1, r).

  Program Definition Verify {S A}
    (w : Pred S A) (m : M S A) : Prop :=
    ordPred (obsPred m) w.

  Program Definition Correct {S A}
    (pre : Pre S)
    (post: Post S A)
    (m : M S A) : Prop :=
    Verify (pp2p (pre, post)) m. 

  Program Definition Incorrect0 {S A}
    (presumes : S -> Prop)
    (* [achieves] works if does not talk about the initial state *)
    (achieves: A -> S -> Prop) 
    (w : Pred S A) : Prop :=
    forall r s1,
      achieves r s1 ->
      exists s0, w s0 r s1 /\ presumes s0.

  Program Definition Incorrect {S A}
    (presumes : S -> Prop)
    (* [achieves] works if does not talk about the initial state *)
    (achieves: A -> S -> Prop) 
    (m : M S A) : Prop :=
    Incorrect0 presumes achieves (obsPred m).

  Example example_3_1_assert : M (nat * nat * nat) unit :=
  '(x, y, z) <- get ;;
  _ <- guard (Nat.even x = true);;
  _ <- guard (negb (Nat.even y) = true);;
  put (x, y, 42).

  Example example_3_1_correct :
    Correct
      (fun '(x, y, z) => Nat.even x = true /\ negb (Nat.even y) = true)
      (fun _ _ '(x, y, z) => z = 42)
      example_3_1_assert.
  Proof.
    unfold Correct, Verify, example_3_1_assert. 
    unfold ordPred, pp2p, ordPost, obsPred.
    intros.
    destruct s0 as [[x y] z].
    destruct s1 as [[x' y'] z'].
    destruct H0.
    simpl in H.
    simpl.
    symmetry.
    assert ((exists
(_ : True) (_ : exists _ : Nat.even x = true, True) (_ : exists
_ : negb (Nat.even y) = true,
True), True)). {
      exists I. 
      exists (ex_intro _ H0 I), (ex_intro _ H1 I).
      constructor.
    }
    apply H in H2.
    injection H2.
    sfirstorder.
  Qed.

  Example example_3_1_incorrect :
    Incorrect
      (fun '(x, y, z) => z = 11)
      (fun _ '(x, y, z) => z = 42)
      example_3_1_assert.
  Proof.
    unfold Incorrect, Incorrect0, ordPred, obsPred, pp2p, ordPost, example_3_1_assert.
    simpl.
    intros.
    destruct r.
    destruct s1 as [[x y] z].
    exists (x, y, 11).
    simpl.
    hauto lq: on drew: off.  
  Qed.

End GuardedPredState.      