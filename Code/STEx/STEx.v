From ExtLib Require Import Monad MonadState StateMonad MonadExc EitherMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import STEx.Examples.

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
Existing Instance Exc_stateT.

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
    sfirstorder.
  Qed.

  Theorem Verify_raise : forall (r : E),
      @Verify S _ R (raise r) (raise r) (@obsSTEx S E).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

    
End Dijkstra.

#[export] Hint Resolve Verify_ret Verify_bind Verify_get Verify_put Verify_raise : mst.

Definition Incorrect {R E S}
  (presumes : S -> Prop)
  (achieves: E + R * S -> Prop)
  (w : STEx S E R) : Prop :=
  forall r,
    achieves r ->
    exists s0, proj1_sig (w s0 (presumes s0) r) /\ presumes s0.
  
Definition IncorrectNormal {R E S}
  (presumes : S -> Prop)
  (achieves: R -> S -> Prop)
  (w : STEx S E R) : Prop :=
  forall r s,
    achieves r s ->
    exists s0, proj1_sig (w s0 (presumes s0) (inr (r, s))) /\ presumes s0.

Definition IncorrectErr {R E S}
  (presumes : S -> Prop)
  (errors: E -> Prop)
  (w : STEx S E R) : Prop :=
  forall e,
    errors e ->
    exists s0, proj1_sig (w s0 (presumes s0) (inl e)) /\ presumes s0.

Definition Incorrect' {R E S}
  (presumes : S -> Prop)
  (achieves: R -> S -> Prop)
  (errors: E -> Prop)
  (w : STEx S E R) : Prop :=
  IncorrectNormal presumes achieves w /\ IncorrectErr presumes errors w. 

Hint Unfold IncorrectNormal IncorrectErr Incorrect Incorrect' : mst.

Module ReadIfIncWrite.

  Definition read_if_inc_write : STEx nat unit unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else raise tt.

  Theorem Incorrect'_read_if_inc_write_less :
    Incorrect' (fun s0 => s0 < 42) (fun _ _ => False) (fun e => e = tt) read_if_inc_write. 
  Proof.
    (* This should be very easy to prove; provable by SMT solvers? *)
    autounfold with mst. cbn; intros. sauto.
  Qed.

  Theorem Incorrect'_read_if_inc_write_more :
    Incorrect' (fun s0 => s0 >= 42) (fun _ s => s > 42) (fun _ => False) read_if_inc_write. 
  Proof.
    (* Is this provable by automatic theorem provers? *)
    autounfold with mst. cbn; intros. split; [ | sauto lq: on drew: off ].
    intros [] s Hs. exists (s - 1). split; try solve [lia]. exists (inr (s - 1 , s - 1)).
    destruct (Nat.leb_spec0 42 (s - 1)); try solve [lia]. cbn. sauto.
  Qed.

  Theorem Verify_read_if_inc_write :
    Verify
      read_if_inc_write
      (* [Examples.read_if_inc_write] is defined the same as
         [read_if_inc_write], except that we use the computation monad
         [state]. *)
      Examples.read_if_inc_write (@obsSTEx nat unit).
  Proof.
    (* This is the Dijkstra monad. *)
    apply Verify_bind; [ auto with mst |].
    intros. destruct (42 <=? a); auto with mst.
  Qed.

  (* This combines the two theorems above and shows that an execution exists
     such that the result state is 0; the trigger presumption is that s0 <
     42. *)
  Theorem Exists_in_obs_less : exists s0,
      proj1_sig (obsSTEx Examples.read_if_inc_write s0 (s0 < 42) (inl tt)).
  Proof.
    pose proof (Incorrect'_read_if_inc_write_less) as HI.
    pose proof (Verify_read_if_inc_write) as HV.
    destruct HI as [Hn He]. specialize (He tt ltac:(reflexivity)).
    destruct He as [s0 [He1 ?]]. exists s0. apply HV. apply He1.
  Qed.

  Theorem Exists_in_obs_more :
    forall s, s > 42 ->
    exists s0, proj1_sig (obsSTEx Examples.read_if_inc_write s0 (s0 >= 42) (inr (tt, s))).
  Proof.
    pose proof (Incorrect'_read_if_inc_write_more) as HI.
    pose proof (Verify_read_if_inc_write) as HV.
    intros. destruct HI as [Hn He]. specialize (Hn tt s H).
    destruct Hn as [s0 [Hn1 ?]]. exists s0. apply HV. apply Hn1.
  Qed.

End ReadIfIncWrite.
