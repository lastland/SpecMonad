Definition SPost A := forall (pre : Prop),
    {p : A -> Prop | forall a, p a -> pre}.

Program Definition SPost_ret {A : Type} (a : A) : SPost A :=
  fun pre =>
    exist _ (fun v => v = a /\ pre) _.
Next Obligation. intros A a pre p. intro H. destruct H. apply H0. Qed.

Definition theta {A} (m:A) : SPost A :=
  SPost_ret m.

(* Definition 1 in original Incorrectness Logic paper **)
Program Definition Incorrect {A} (presumes : Prop) (m : A) (achieves: A -> Prop)  : Prop :=
  forall r, achieves r -> (proj1_sig (theta m presumes)) r.

Definition example_3_1 (x y z : nat) : nat :=
  if Nat.even x then
    if negb (Nat.even y) then 42 else z
  else z.

From Hammer Require Import Hammer Tactics.

Example example_3_1_test1 :
  forall x y z,
    Incorrect
      (z = 11)
      (example_3_1 x y z)
      (fun r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  intros x y z.
  unfold Incorrect. unfold example_3_1.
  split.
  - sauto lq: on.
  - exfalso. admit. (* This branch is unprovable *)
Admitted.

Example example_3_1_test2 :
  forall x y z,
    Incorrect
      (True)
      (example_3_1 x y z)
      (fun r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  intros x y z.
  unfold Incorrect. unfold example_3_1.
  split.
  - hauto lq: on drew: off.
  - trivial.
Qed.

Example example_3_1_test3 :
  forall x y z,
    not (Incorrect (z = 11) (example_3_1 x y z) (fun r => r = 42)).
Proof.
Admitted.
