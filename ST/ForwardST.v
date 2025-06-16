From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.SPost ST.STExamples.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Set Implicit Arguments.

Section Types.

  Variable S A : Type.

  Definition ST := forall (s0 : S) (pre : Prop), 
      {p : A -> S -> Prop | forall a s, p a s -> pre}.

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

Program Definition Verify {S R}
  (w : ST S R) (m : state S R)
  (obs: forall {R}, state S R -> ST S R) : Prop :=
  forall s0 pre r s,
    w s0 pre r s -> obs m s0 pre r s.

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

Program Definition Incorrect {S R}
  (w : ST S R) (m : state S R)
  (obs: forall {R}, state S R -> ST S R) : Prop :=
  forall s0 pre r s,
    obs m s0 pre r s ->
    w s0 pre r s.
 
#[local] Hint Unfold Incorrect : mst.

Section Incorrect.

  Variable S A R: Type.

  Theorem Incorrect_ret : forall (r : R),
      @Incorrect S _ (ret r) (ret r) (@obsST S).
  Proof. autounfold with mst. hauto. Qed.

  Theorem Incorrect_bind : forall m1 m2 k1 k2,
      @Incorrect S A m1 m2 (@obsST S) ->
      (forall a, @Incorrect S R (k1 a) (k2 a) (@obsST S)) ->
      @Incorrect S R (m1 >>= k1) (m2 >>= k2) (@obsST S).
  Proof.
    autounfold with mst. hauto lq: on drew: off.
  Qed.

  Theorem Incorrect_get :
    @Incorrect S _ get get (@obsST S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Incorrect_put : forall (s : S),
    Incorrect (put s) (put s) (@obsST S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

End Incorrect.

Module ReadIncWrite.

  Definition read_inc_write : ST nat unit :=
    x <- get ;; put (x + 1).

  Program Definition obsNatOver (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ s >= 1.

  Program Definition obsNatUnder (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (runState m s0 = (r, s) \/ (s0 = 0 /\ s = 1)) /\ pre.

  Theorem Verify_read_inc_write :
    Verify read_inc_write STExamples.read_inc_write obsNatOver.
  Proof.
    autounfold with mst. fcrush.
  Qed.
  
  Theorem Incorrect_read_inc_write :
    Incorrect read_inc_write STExamples.read_inc_write obsNatUnder.
  Proof.
    autounfold with mst.
    hauto lq: on drew: off.
  Qed.

End ReadIncWrite.

Module ReadIfIncWrite.

  Definition read_if_inc_write : ST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Program Definition obsNatOver (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ s >= 0.

  Program Definition obsNatOver' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ (s0 >= 42 -> s = s0 + 1).

  Program Definition obsNatUnder (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (runState m s0 = (r, s) \/ (s0 < 42 /\ s = 0)) /\ pre.

  Program Definition obsNatUnder' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (runState m s0 = (r, s) \/ (s0 >= 42 /\ s = s0 + 1)) /\ pre.

  Program Definition obsNatUnder'' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (runState m s0 = (r, s) \/ False) /\ pre.

  Theorem Verify_read_if_inc_write :
    Verify
      read_if_inc_write
      STExamples.read_if_inc_write obsNatOver.
  Proof.
    autounfold with mst. cbn. intros.
    destruct H as [a [s' H]].
    destruct (Nat.leb_spec0 42 s0);
      destruct (Nat.leb_spec0 42 a);
      cbn in *; fcrush.
  Qed.

  Theorem Verify_read_if_inc_write' :
    Verify
      read_if_inc_write
      STExamples.read_if_inc_write obsNatOver'.
  Proof.
    autounfold with mst. cbn. intros.
    destruct H as [a [s' H]].
    destruct (Nat.leb_spec0 42 s0);
      destruct (Nat.leb_spec0 42 a);
      cbn in *; fcrush.
  Qed.

  Theorem Incorrect_read_if_inc_write :
    Incorrect
      read_if_inc_write
      STExamples.read_if_inc_write obsNatUnder.
  Proof.
    autounfold with mst. cbn; intros. exists s0.
    destruct (Nat.leb_spec0 42 s0);
      cbn in *; hauto.
  Qed.

  Theorem Incorrect_read_if_inc_write' :
    Incorrect
      read_if_inc_write
      STExamples.read_if_inc_write obsNatUnder'.
  Proof.
    autounfold with mst. cbn; intros. exists s0.
    destruct (Nat.leb_spec0 42 s0);
      cbn in *; hauto.
  Qed.

  Theorem Incorrect_read_if_inc_write'' :
    Incorrect
      read_if_inc_write
      STExamples.read_if_inc_write obsNatUnder''.
  Proof.
    autounfold with mst. cbn; intros. exists s0.
    destruct (Nat.leb_spec0 42 s0);
      cbn in *; hauto.
  Qed.

End ReadIfIncWrite.

Module ReadIfIncWrite2.

  Definition read_if_inc_write2 : ST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 42.

  Program Definition obsNatOver (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ s >= 42.

  Program Definition obsNatOver' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ (s0 >= 42 -> s = s0 + 1).

  Program Definition obsNatUnder (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (s0 < 42 /\ s = 42) /\ pre.

  Program Definition obsNatUnder' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (s0 >= 42 /\ s = s0 + 1) /\ pre.

  Program Definition obsNatUnder'' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => False /\ pre.

  Program Definition obsNatUnder''' (R : Type) (m : state nat R) : ST nat R :=
    fun s0 pre r s => (s0 < 42 /\ s = 0) /\ pre.

  Theorem Verify_read_if_inc_write2 :
    Verify
      read_if_inc_write2
      STExamples.read_if_inc_write2 obsNatOver.
  Proof.
    autounfold with mst. cbn. intros.
    destruct H as [a [s' H]].
    destruct (Nat.leb_spec0 42 s0);
      destruct (Nat.leb_spec0 42 a);
      cbn in *; fcrush.
  Qed.

  Theorem Verify_read_if_inc_write2' :
    Verify
      read_if_inc_write2
      STExamples.read_if_inc_write2 obsNatOver'.
  Proof.
    autounfold with mst. cbn. intros.
    destruct H as [a [s' H]].
    destruct (Nat.leb_spec0 42 s0);
      destruct (Nat.leb_spec0 42 a);
      cbn in *; fcrush.
  Qed.

  Theorem Incorrect_read_if_inc_write2 :
    Incorrect
      read_if_inc_write2
      STExamples.read_if_inc_write2 obsNatUnder.
  Proof.
    autounfold with mst. sauto.
  Qed.

  Theorem Incorrect_read_if_inc_write2' :
    Incorrect
      read_if_inc_write2
      STExamples.read_if_inc_write2 obsNatUnder'.
  Proof.
    autounfold with mst. sauto.
  Qed.

  Theorem Incorrect_read_if_inc_write2'' :
    Incorrect
      read_if_inc_write2
      STExamples.read_if_inc_write2 obsNatUnder''.
  Proof.
    autounfold with mst. hauto.
  Qed.

  Theorem Incorrect_read_if_inc_write2''' :
    Incorrect
      read_if_inc_write2
      STExamples.read_if_inc_write2 obsNatUnder'''.
  Proof.
    autounfold with mst. cbn; intros. exists s0.
    destruct (Nat.leb_spec0 42 s0);
      cbn in *.
    - fcrush.
    - exists s0. (* Not provable *)
  Abort.

End ReadIfIncWrite2.

Program Definition Incorrect' {R S}
  (presumes : S -> Prop)
  (achieves: S -> R -> S -> Prop)
  (w : ST S R) : Prop :=
    (forall s0 r s, presumes s0 ->
               achieves s0 r s ->
               w s0 (presumes s0) r s) /\
      exists s0, presumes s0.

Hint Unfold Incorrect' : mst.

Module ReadIfIncWrite'.

  Definition read_if_inc_write : ST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Theorem Incorrect_read_if_inc_write_less :
    Incorrect' (fun s0 => s0 < 42) (fun _ _ s => s = 0) read_if_inc_write. 
  Proof.
    (* This should be very easy to prove; provable by SMT solvers? *)
    autounfold with mst. sauto.
  Qed.
      
  Theorem Verify_read_if_inc_write :
    Verify
      read_if_inc_write
      (* [STExamples.read_if_inc_write] is defined the same as
         [read_if_inc_write], except that we use the computation monad
         [state]. *)
      STExamples.read_if_inc_write (@obsST nat).
  Proof.
    (* This is the Dijkstra monad. *)
    eapply Verify_bind.
    - apply Verify_get.
    - intros. destruct (Nat.leb_spec0 42 a); apply Verify_put.
  Qed.

  (* This combines the two theorems above and shows that an execution exists
     such that the result state is 0; the trigger presumption is that s0 <
     42. *)
  Theorem Exists_in_obs : forall r, exists s0,
      proj1_sig (obsST STExamples.read_if_inc_write s0 (s0 < 42)) r 0.
  Proof.
    pose proof (Incorrect_read_if_inc_write_less) as HI.
    pose proof (Verify_read_if_inc_write) as HV.
    intros r. destruct HI as [Hunder [s0 Hpre]].
    exists s0. auto.
  Qed.

End ReadIfIncWrite'.
