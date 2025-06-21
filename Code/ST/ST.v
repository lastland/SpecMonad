From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.Examples.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition ST := forall (s0 : S) (pre : Prop),
      A -> S -> {p : Prop | p -> pre}.

End Types.

Section ST.

  Variable S : Type.
  
  Program Definition retST {A} (a : A) : ST S A :=
    fun s0 pre r s => pre /\ r = a /\ s0 = s.
  
  Program Definition bindST {A B}
    (m : ST S A) (k : A -> ST S B) : ST S B :=
    fun s0 pre b s => exists a s', k a s' (m s0 pre a s') b s.
  Next Obligation. sfirstorder. Qed.

  Program Definition getST : ST S S :=
    fun s0 pre r s => pre /\ r = s0 /\ s = s0. 

  Program Definition putST (s : S) : ST S unit :=
    fun _ pre _ s' => pre /\ s = s'. 

  #[global] Instance Monad__ST : Monad (ST S) :=
    {| ret := fun _ => retST ;
       bind := fun _ _ => bindST |}.

  #[global] Instance MonadState__ST : MonadState S (ST S) :=
    {| get := getST ;
       put := putST |}.

  (* Monad laws not proven. Not using [SProp]. *)

End ST.

Program Definition obsST (S R : Type) (m : state S R) : ST S R :=
  fun s0 pre r s => runState m s0 = (r, s) /\ pre.

Definition Verify {S R}
  (w : ST S R) (m : state S R)
  (obs: forall {R}, state S R -> ST S R) : Prop :=
  forall s0 pre r s,
    proj1_sig (w s0 pre r s) -> proj1_sig (obs m s0 pre r s).

#[local] Hint Unfold retST bindST getST putST Verify: mst.

Section Dijkstra.

  Variables S A R : Type.

  Theorem Verify_ret : forall (r : R),
      @Verify S _ (ret r) (ret r) (@obsST S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_bind : forall m1 m2 k1 k2,
      @Verify S A m1 m2 (@obsST S) ->
      (forall a, @Verify S R (k1 a) (k2 a) (@obsST S)) ->
      @Verify S R (m1 >>= k1) (m2 >>= k2) (@obsST S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.

  Theorem Verify_get :
    @Verify S _ get get (@obsST S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_put : forall (s : S),
    Verify (put s) (put s) (@obsST S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.
    
End Dijkstra.

#[export] Hint Resolve Verify_ret Verify_bind Verify_get Verify_put : mst.

Definition Incorrect {R S}
  (presumes : S -> Prop)
  (achieves: S -> R -> S -> Prop)
  (w : ST S R) : Prop :=
  forall r s, exists s0,
    (presumes s0 -> achieves s0 r s ->
     proj1_sig (w s0 (presumes s0) r s)) /\
      presumes s0.

Hint Unfold Incorrect : mst.

Module ReadIfIncWrite.

  Definition read_if_inc_write : ST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Theorem Incorrect_read_if_inc_write_less :
    Incorrect (fun s0 => s0 < 42) (fun _ _ s => s = 0) read_if_inc_write. 
  Proof.
    (* This should be very easy to prove; provable by SMT solvers? *)
    autounfold with mst. cbn; intros. sauto.
  Qed.
      
  Theorem Verify_read_if_inc_write :
    Verify
      read_if_inc_write
      (* [Examples.read_if_inc_write] is defined the same as
         [read_if_inc_write], except that we use the computation monad
         [state]. *)
      Examples.read_if_inc_write (@obsST nat).
  Proof.
    (* This is the Dijkstra monad. *)
    apply Verify_bind.
    - apply Verify_get.
    - intros. destruct (42 <=? a); apply Verify_put.
  Qed.

  (* This combines the two theorems above and shows that an execution exists
     such that the result state is 0; the trigger presumption is that s0 <
     42. *)
  Theorem Exists_in_obs : forall r, exists s0,
      proj1_sig (obsST Examples.read_if_inc_write s0 (s0 < 42) r 0).
  Proof.
    pose proof (Incorrect_read_if_inc_write_less) as HI.
    pose proof (Verify_read_if_inc_write) as HV.
    intros r. specialize (HI r 0). destruct HI as [s0 [? ?]].
    exists s0. auto.
  Qed.

End ReadIfIncWrite.

(* We can prove the following is true for [ret]s, but not for [bind]s. *)

Theorem weaken_pre_ret :
  forall {S R} P P' Q (r : R),
  Incorrect P Q (ret r) ->
  (forall (s : S), P s -> P' s) ->
  Incorrect P' Q (ret r).
Proof.
  autounfold with mst. intros.
  specialize (H r0 s). destruct H as [s0 [? ?]].
  exists s0. hauto lq: on.
Qed.

Theorem strengthen_post_ret :
  forall {S R} P Q Q' (r : R),
  Incorrect P Q (ret r) ->
  (forall r (s0 s : S), Q' s0 r s -> Q s0 r s) ->
  Incorrect P Q' (ret r).
Proof.
  autounfold with mst. intros.
  specialize (H r0 s). destruct H as [s0 [? ?]].
  exists s0. sfirstorder.
Qed.
