From ExtLib Require Import Monad MonadReader ReaderMonad MonadLaws.
From Hammer Require Import Tactics.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition Reader := forall (s0 : S) (pre : Prop), 
      {p : A -> Prop | forall a, p a -> pre}.

  Definition WFReader :=
    { w : Reader | forall s0 p q r,
        (p -> q) -> proj1_sig (w s0 p) r -> proj1_sig (w s0 q) r }.

End Types.

Section Reader.

  Variable S : Type.
  
  Program Definition retReader {A} (a : A) : Reader S A :=
    fun _ pre r => pre /\ r = a.
  
  Program Definition bindReader {A B}
    (m : Reader S A) (k : A -> Reader S B) : Reader S B :=
    fun s0 pre b => exists a, k a s0 (m s0 pre a) b.
  Next Obligation. sfirstorder. Qed.

  Program Definition askReader : Reader S S :=
    fun s0 pre r => pre /\ r = s0.

  Program Definition localReader {A}
    (f : S -> S) (m : Reader S A): Reader S A :=
    fun s0 => m (f s0).

  #[global] Instance Monad__Reader : Monad (Reader S) :=
    {| ret := fun _ => retReader ;
       bind := fun _ _ => bindReader |}.

  #[global] Instance MonadReader__Reader : MonadReader S (Reader S) :=
    {| ask   := askReader ;
       local := @localReader |}.

  (* Monad laws not proven. Not using [SProp]. *)

End Reader.

Program Definition obsReader (S R : Type) (m : reader S R) : Reader S R :=
  fun s0 pre r => runReader m s0 = r /\ pre.

Program Definition Verify {S R}
  (w : Reader S R) (m : reader S R)
  (obs: forall {R}, reader S R -> Reader S R) : Prop :=
  forall s0 pre r, w s0 pre r -> obs m s0 pre r.

#[local] Hint Unfold retReader bindReader localReader askReader Verify: mst.

Section Dijkstra.

  Variables S A R : Type.

  Theorem Verify_ret : forall (r : R),
      @Verify S _ (ret r) (ret r) (@obsReader S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_bind : forall m1 m2 k1 k2,
      @Verify S A m1 m2 (@obsReader S) ->
      (forall a, @Verify S R (k1 a) (k2 a) (@obsReader S)) ->
      @Verify S R (m1 >>= k1) (m2 >>= k2) (@obsReader S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.

  Theorem Verify_ask :
    @Verify S _ ask ask (@obsReader S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_local : forall (f : S -> S) (m1 : Reader S A) m2,
      Verify m1 m2 (@obsReader S) ->
      Verify (local f m1) (local f m2) (@obsReader S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.
    
End Dijkstra.

#[export] Hint Resolve Verify_ret Verify_bind Verify_ask Verify_local : mst.

Program Definition Incorrect {R S}
  (presumes : S -> Prop)
  (w : Reader S R) 
  (achieves: S -> R -> Prop) : Prop :=
  forall r, exists s0,
    (presumes s0 -> achieves s0 r ->
     w s0 (presumes s0) r) /\
      presumes s0.

Hint Unfold Incorrect : mst.

Definition example_3_1r : reader (nat * nat * nat) nat :=
  '(x, y, z) <- ask ;;
  if Nat.even x then
    if negb (Nat.even y) then ret 42 else ret z
  else ret z.

Definition example_3_1R : Reader (nat * nat * nat) nat :=
  '(x, y, z) <- ask ;;
  if Nat.even x then
    if negb (Nat.even y) then ret 42 else ret z
  else ret z.
  
Example example_3_1_test1 :
    Incorrect
      (fun '(x, y, z) => z = 11)
      example_3_1R
      (fun '(x, y, z) r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  autounfold with mst. cbn; intros.
  exists (0, 1, 11). split; auto.
  cbn; intros. exists (0, 1, 11).
  hauto lq: on drew: off.
Qed.

Theorem example_3_1_dijkstra :
  Verify example_3_1R example_3_1r (@obsReader (nat * nat * nat)%type).
Proof.
  unfold example_3_1R, example_3_1r.
  apply Verify_bind; [ apply Verify_ask | ].
  intros [[? ?] ?].
  destruct (Nat.even n) eqn:Hn; [ | apply Verify_ret ].
  destruct (Nat.even n0) eqn:Hn0; cbn; apply Verify_ret.
Qed.
Module Test2.

  Definition example_3_1R : Reader (nat * nat * nat) (nat * nat * nat) :=
    '(x, y, z) <- ask ;;
    if Nat.even x then
      if negb (Nat.even y) then ret (x, y, 42) else ret (x, y, z)
    else ret (x, y, z).

  Example example_3_1_test1 :
    Incorrect
      (fun '(x, y, z) => z = 11)
      example_3_1R
      (fun _ '(x, y, z) =>
         z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
  Proof.
    autounfold with mst. cbn; intros.
    exists (0, 1, 11). split; auto.
    cbn; intros. exists (0, 1, 11).
    destruct r. destruct p.
    destruct H. destruct H0. simpl.
    hauto lq: on drew: off.
  Qed.

  Example example_3_1_test2 : (** should be unprovable *)
    Incorrect
      (fun '(x, y, z) => z = 11)
      example_3_1R
      (fun '(x0,y0,z0) '(x, y, z) => z = 42 /\ x0 = x /\ y0 = y).
  Proof.
    autounfold with mst. cbn; intros.
    exists (0, 1, 11). split; auto.
    cbn; intros. exists (0, 1, 11).
    hauto lq: on drew: off.
  Qed.

End Test2.
