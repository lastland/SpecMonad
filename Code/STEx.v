From ExtLib Require Import Monad MonadState StateMonad MonadExc EitherMonad MonadLaws.
From Hammer Require Import Hammer Tactics.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S E A : Type.

  Definition STEx := forall (s0 : S) (pre : Prop),
      E + A * S -> {p : Prop | p -> pre}.

End Types.

Section STEx.

  Variable S E : Type.
  
  Program Definition retSTEx {A} (a : A) : STEx S E A :=
    fun s0 pre r => pre /\ r = inr (a, s0).

  (* Somehow type check fails if I define this directly, so I have to use the proof mode. *)
  Definition bindSTEx {A B}
    (m : STEx S E A) (k : A -> STEx S E B) : STEx S E B.
  intros s0 pre r.
  eapply exist with (x:=exists a,
                        match a with
                        | inr (v, s') => proj1_sig (k v s' (proj1_sig (m s0 pre a)) r)
                        | inl e => proj1_sig (m s0 pre (inl e)) /\ r = inl e
                        end).
  sauto.
  Defined.

  Program Definition getSTEx : STEx S E S :=
    fun s0 pre r => pre /\ r = inr (s0, s0).

  Program Definition putSTEx (s : S) : STEx S E unit :=
    fun _ pre r => pre /\ r = inr (tt, s).

  Program Definition raiseSTEx {A} (e : E) : STEx S E A :=
    fun s0 pre r => pre /\ r = inl e. 

  (* Somehow type check fails if I define this directly, so I have to use the proof mode. *)
  Definition catchSTEx {A}
    (m : STEx S E A) (c : E -> STEx S E A) : STEx S E A.
  intros s0 pre r.
  apply exist with (x:=exists a,
                       match a with
                       | inl e => proj1_sig (c e s0 (proj1_sig (m s0 pre (inl e))) r)
                       | inr (v, s1) => proj1_sig (m s0 pre r) /\ r = inr (v, s1)
                       end).
  sauto.
  Defined.

  #[global] Instance Monad__STEx : Monad (STEx S E) :=
    {| ret := fun _ => retSTEx ;
       bind := fun _ _ => bindSTEx |}.

  #[global] Instance MonadState__STEx : MonadState S (STEx S E) :=
    {| get := getSTEx ;
       put := putSTEx |}.

  #[global] Instance MonadExc__STEx : MonadExc E (STEx S E) :=
    {| raise := fun _ => raiseSTEx ;
       catch := fun _ => catchSTEx |}.

  (* Monad laws not proven. Not using [SProp]. *)

End STEx.

Program Definition obsSTEx (S E R : Type)
  (m : stateT S (sum E) R) : STEx S E R :=
  fun s0 pre r => runStateT m s0 = r /\ pre.

Definition Verify {S E R}
  (w : STEx S E R) (m : stateT S (sum E) R)
  (obs: forall {R}, stateT S (sum E) R -> STEx S E R) : Prop :=
  forall s0 pre r,
    proj1_sig (w s0 pre r) -> proj1_sig (obs m s0 pre r).

#[local] Hint Unfold retSTEx bindSTEx getSTEx putSTEx raiseSTEx catchSTEx Verify: mst.

Existing Instance Monad_stateT.

Section Dijkstra.

  Variables S E A R : Type.

  Theorem Verify_ret : forall (r : R),
      @Verify S _ _ (ret r) (ret r) (@obsSTEx S E).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_bind : forall m1 m2 k1 k2,
      @Verify S E A m1 m2 (@obsSTEx S E) ->
      (forall a, @Verify S E R (k1 a) (k2 a) (@obsSTEx S E)) ->
      @Verify S E R (m1 >>= k1) (m2 >>= k2) (@obsSTEx S E).
  Proof.
    autounfold with mst. cbn; intros.
    destruct H1 as [[e | [a s]] H1]; sauto lq:on.
  Qed.

  Theorem Verify_get :
    @Verify S E _ get get (@obsSTEx S E).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_put : forall (s : S),
    Verify (put s) (put s) (@obsSTEx S E).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.
    
End Dijkstra.

#[export] Hint Resolve Verify_ret Verify_bind Verify_get Verify_put : mst.

Definition Incorrect {R S}
  (presumes : S -> Prop)
  (achieves: S -> R -> S -> Prop)
  (w : STEx S R) : Prop :=
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
      (* [STExamples.read_if_inc_write] is defined the same as
         [read_if_inc_write], except that we use the computation monad
         [state]. *)
      STExamples.read_if_inc_write (@obsST nat).
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
      proj1_sig (obsST STExamples.read_if_inc_write s0 (s0 < 42) r 0).
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
