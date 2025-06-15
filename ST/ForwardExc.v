From ExtLib Require Import Monad MonadExc EitherMonad.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.SPost.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Existing Instance Monad_either.
Existing Instance Exception_either.

Set Implicit Arguments.

Definition Exc (E A : Type) :=
  forall (pre : Prop), E + A -> {p : Prop | p -> pre}.

Section Exc.

  Variable E : Type.
  
  Program Definition retExc {A} (a : A) : Exc E A :=
    fun pre r => pre /\ r = inr a.
  
  Program Definition bindExc {A B}
    (m : Exc E A) (k : A -> Exc E B) : Exc E B :=
    fun pre r => exists a, match a with
                   | inl e => m pre a /\ r = inl e
                   | inr v => k v (m pre a) r
                   end.
  Next Obligation. sauto. Qed.

  Program Definition raiseExc {A} (e : E) : Exc E A :=
    fun pre r => pre /\ r = inl e.

  Program Definition catchExc {A}
    (m : Exc E A) (c : E -> Exc E A) : Exc E A :=
    fun pre r => exists a, match a with
                  | inl e => c e (m pre a) r
                  | inr v => m pre a /\ r = inr v
                  end.
  Next Obligation. sauto. Qed.

  #[global] Instance Monad__Exc : Monad (Exc E) :=
    {| ret := fun _ => retExc ;
       bind := fun _ _ => bindExc |}.

  #[global] Instance MonadExc__Exc : MonadExc E (Exc E) :=
    {| raise := fun _ => raiseExc ;
       catch := fun _ => catchExc |}.

  (* Monad laws not proven. Not using [SProp]. *)

End Exc.

Program Definition obsNeverFail (E R : Type) (m : sum E R) : Exc E R :=
  match m with
  | inl e => fun pre r => False
  | inr a => fun pre r => r = inr a /\ pre
  end.
Next Obligation. contradiction. Qed.

Program Definition obsFineToFail (E R : Type) (m : sum E R) : Exc E R :=
  fun pre r => m = r /\ pre.

Program Definition obsAlwaysSucc (E R : Type) (m : sum E R) : Exc E R :=
  match m with
  | inl e => fun pre r => pre
  | inr a => fun pre r => r = inr a /\ pre
  end.

Program Definition Verify {E R}
  (w : Exc E R) (m : sum E R)
  (obs: forall {R}, sum E R -> Exc E R) : Prop :=
  forall pre r, proj1_sig (w pre r) -> proj1_sig (obs m pre r).

#[local] Hint Unfold retExc bindExc raiseExc catchExc Verify: mst.

Section Dijkstra.

  Variables E A R : Type.

  Theorem Verify_ret' : forall (r : R),
      @Verify E _ (ret r) (ret r) (@obsNeverFail E).
  Proof.
    autounfold with mst. hauto lq: on drew: off.
  Qed.

  Theorem Verify_ret : forall (r : R),
      @Verify E _ (ret r) (ret r) (@obsFineToFail E).
  Proof.
    autounfold with mst. sfirstorder.
  Qed.

  Theorem Verify_bind : forall m1 m2 k1 k2,
      @Verify E A m1 m2 (@obsFineToFail E) ->
      (forall a, @Verify E R (k1 a) (k2 a) (@obsFineToFail E)) ->
      @Verify E R (m1 >>= k1) (m2 >>= k2) (@obsFineToFail E).
  Proof.
    autounfold with mst. cbn; intros.
    sauto lq: on drew: off.
  Qed.

  Theorem Verify_bind' : forall m1 m2 k1 k2,
      @Verify E A m1 m2 (@obsNeverFail E) ->
      (forall a, @Verify E R (k1 a) (k2 a) (@obsNeverFail E)) ->
      @Verify E R (m1 >>= k1) (m2 >>= k2) (@obsNeverFail E).
  Proof.
    autounfold with mst. cbn; intros.
    destruct H1 as [a H1].
    destruct m2; cbn in *.
    - (* m2 has an exception. *)
      specialize (H pre a). sauto.
    - (* m2 runs normally *)
      destruct a.
      + (* a is an exception *) hauto lq: on.
      + (* a is a value *)
        assert (proj1_sig (m1 pre (inr a))) by sfirstorder.
        specialize (H pre (inr a) H2). destruct H; inversion H; subst.
        (* Now we know a and a0 are the same. *)
        specialize (H0 a0 _ _ H1). 
        destruct (k2 a0) eqn:Hk2; cbn in *; sfirstorder.
  Qed.

  Theorem Verify_raise : forall (e : E),
      @Verify _ A (raise e) (raise e) (@obsFineToFail E).
  Proof.
    autounfold with mst. sfirstorder.
  Qed.

  Theorem Verify_raise' : forall (e : E),
      @Verify _ A (raise e) (raise e) (@obsNeverFail E).
  Proof.
    autounfold with mst. cbn; intros.
    (* Not provable, as it should be! *)
  Abort.

  Theorem Verify_catch : forall m1 m2 k1 k2,
      @Verify E A m1 m2 (@obsFineToFail E) ->
      (forall a, @Verify E A (k1 a) (k2 a) (@obsFineToFail E)) ->
      @Verify E A (catch m1 k1) (catch m2 k2) (@obsFineToFail E).
  Proof.
    autounfold with mst. cbn; intros.
    hauto lq: on drew: off.
  Qed.

  Theorem Verify_catch' : forall m1 m2 k1 k2,
      @Verify E A m1 m2 (@obsNeverFail E) ->
      (forall a, @Verify E A (k1 a) (k2 a) (@obsNeverFail E)) ->
      @Verify E A (catch m1 k1) (catch m2 k2) (@obsNeverFail E).
  Proof.
    autounfold with mst. cbn; intros.
    destruct H1 as [a H1].
    destruct m2; cbn in *.
    - (* m2 has an exception. *)
      specialize (H pre a). sauto.
    - (* m2 runs normally *)
      destruct a.
      + (* a is an exception *)
        assert (proj1_sig (m1 pre (inl e))) by sfirstorder.
        specialize (H pre (inl e) H2). sfirstorder.
      + (* a is a value *)
        sauto lq: on.
  Qed.
  
End Dijkstra.

Program Definition Incorrect {E R}
  (w : Exc E R) (m : sum E R)
  (obs: forall {R}, sum E R -> Exc E R) : Prop :=
  forall pre r, proj1_sig (obs m pre r) -> proj1_sig (w pre r).
 
#[local] Hint Unfold Incorrect : mst.

Section Incorrect.

  Variable E A R: Type.

  Theorem Incorrect_ret : forall (r : R),
      @Incorrect E _ (ret r) (ret r) (@obsFineToFail E).
  Proof. autounfold with mst. sfirstorder. Qed.

  Theorem Incorrect_ret' : forall (r : R),
      @Incorrect E _ (ret r) (ret r) (@obsNeverFail E).
  Proof. autounfold with mst. sauto lq: on. Qed.

  Theorem Incorrect_bind : forall m1 m2 k1 k2,
      @Incorrect E A m1 m2 (@obsFineToFail E) ->
      (forall a, @Incorrect E R (k1 a) (k2 a) (@obsFineToFail E)) ->
      @Incorrect E R (m1 >>= k1) (m2 >>= k2) (@obsFineToFail E).
  Proof.
    autounfold with mst. sauto q: on.
  Qed.

  Theorem Incorrect_bind' : forall m1 m2 k1 k2,
      @Incorrect E A m1 m2 (@obsNeverFail E) ->
      (forall a, @Incorrect E R (k1 a) (k2 a) (@obsNeverFail E)) ->
      @Incorrect E R (m1 >>= k1) (m2 >>= k2) (@obsNeverFail E).
  Proof.
    autounfold with mst. cbn; intros. destruct m2.
    - (* m2 has an exception *)
      cbn in *. contradiction.
    - (* m2 runs normally *)
      exists (inr a). destruct (k2 a) eqn:Hk2.
      + cbn in H1; contradiction.
      + cbn in *. destruct H1; subst. 
        apply H0. rewrite Hk2; cbn. sauto lq: on.
  Qed.

  Theorem Incorrect_raise : forall (e : E),
      @Incorrect _ A (raise e) (raise e) (@obsFineToFail E).
  Proof.
    autounfold with mst. sfirstorder.
  Qed.

  Theorem Incorrect_raise' : forall (e : E),
      @Incorrect _ A (raise e) (raise e) (@obsNeverFail E).
  Proof.
    autounfold with mst. sfirstorder.
    (* Easy because "ex falso"! *)
  Qed.

  Theorem Incorrect_catch : forall m1 m2 k1 k2,
      @Incorrect E A m1 m2 (@obsFineToFail E) ->
      (forall a, @Incorrect E A (k1 a) (k2 a) (@obsFineToFail E)) ->
      @Incorrect E A (catch m1 k1) (catch m2 k2) (@obsFineToFail E).
  Proof.
    autounfold with mst. cbn; intros. sauto q: on.
  Qed.

  Theorem Incorrect_catch' : forall m1 m2 k1 k2,
      @Incorrect E A m1 m2 (@obsNeverFail E) ->
      (forall a, @Incorrect E A (k1 a) (k2 a) (@obsNeverFail E)) ->
      @Incorrect E A (catch m1 k1) (catch m2 k2) (@obsNeverFail E).
  Proof.
    autounfold with mst. cbn; intros. destruct m2.
    - (* m2 has an exception. *)
      cbn in *. exists (inl e). destruct (k2 e) eqn:Hk2.
      + (* catches an exception, but returns an exception *)
        cbn in H1. contradiction.
      + (* catches an exception, but returns a normal value *)
        cbn in *. destruct H1; subst.
        apply H0. rewrite Hk2; cbn. split; auto.
        apply H. (* Does not seem provable *)
        admit.
    - (* m2 is a value *)
      exists (inr a). cbn in *. sauto lq: on.
  Abort.

  Theorem Incorrect_ret'' : forall (r : R),
      @Incorrect E _ (ret r) (ret r) (@obsAlwaysSucc E).
  Proof. autounfold with mst. sfirstorder. Qed.

  Theorem Incorrect_bind'' : forall m1 m2 k1 k2,
      @Incorrect E A m1 m2 (@obsAlwaysSucc E) ->
      (forall a, @Incorrect E R (k1 a) (k2 a) (@obsAlwaysSucc E)) ->
      @Incorrect E R (m1 >>= k1) (m2 >>= k2) (@obsAlwaysSucc E).
  Proof.
    autounfold with mst. cbn; intros. destruct m2; cbn in *.
    - (* m2 has an exception *)
      exists (inl e). split; auto. (* not provable *)
  Abort.

End Incorrect.

(*)
Module ReadIncWrite.

  Definition read_inc_write : Exc nat unit :=
    x <- get ;; put (x + 1).

  Program Definition obsNatOver (R : Type) (m : state nat R) : Exc nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ s >= 1.

  Program Definition obsNatUnder (R : Type) (m : state nat R) : Exc nat R :=
    fun s0 pre r s => (runState m s0 = (r, s) \/ (s0 = 0 /\ s = 1)) /\ pre.

  Theorem Verify_read_inc_write :
    Verify read_inc_write ExcExamples.read_inc_write obsNatOver.
  Proof.
    autounfold with mst. fcrush.
  Qed.
  
  Theorem Incorrect_read_inc_write :
    Incorrect read_inc_write ExcExamples.read_inc_write obsNatUnder.
  Proof.
    autounfold with mst.
    hauto lq: on drew: off.
  Qed.

End ReadIncWrite.

Module ReadIfIncWrite.

  Definition read_if_inc_write : Exc nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Program Definition obsNatOver (R : Type) (m : state nat R) : Exc nat R :=
    fun s0 pre r s => runState m s0 = (r, s) /\ pre /\ s >= 0.

  Program Definition obsNatUnder (R : Type) (m : state nat R) : Exc nat R :=
    fun s0 pre r s => (runState m s0 = (r, s) \/ (s0 = 0 /\ s = 0)) /\ pre.

  Theorem Verify_read_inc_write :
    Verify
      read_if_inc_write
      ExcExamples.read_if_inc_write obsNatOver.
  Proof.
    autounfold with mst. cbn. intros.
    destruct H as [a [s' H]].
    destruct (Nat.leb_spec0 42 s0);
      destruct (Nat.leb_spec0 42 a);
      cbn in *; fcrush.
  Qed.
  
  Theorem Incorrect_read_inc_write :
    Incorrect
      read_if_inc_write
      ExcExamples.read_if_inc_write obsNatUnder.
  Proof.
    autounfold with mst. cbn; intros. exists s0.
    destruct (Nat.leb_spec0 42 s0);
      cbn in *; sauto lq: on.
  Qed.

End ReadIfIncWrite.
*)
