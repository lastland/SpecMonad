From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.STExamples ST.ST.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition WFST :=
    { w : ST S A | forall s0 p q r s,
        (p -> q) -> proj1_sig (w s0 p) r s -> proj1_sig (w s0 q) r s  }.

End Types.

Section WFST.

  Variable S : Type.
  
  Program Definition retWFST {A} (a : A) : WFST S A :=
    retST a.
  
  Program Definition bindWFST {A B}
    (m : WFST S A) (k : A -> WFST S B) : WFST S B :=
    bindST m k.
  Next Obligation.
    destruct m as [m Hp]; cbn in *.
    exists H0. exists H1. destruct (k H0) as [ka Hkp] eqn:Hk.
    cbn in *. eapply Hkp; eauto.
  Qed.

  Program Definition getWFST : WFST S S :=
    @getST S.

  Program Definition putWFST (s : S) : WFST S unit :=
    putST s.

  #[global] Instance Monad__WFST : Monad (WFST S) :=
    {| ret := fun _ => retWFST ;
       bind := fun _ _ => bindWFST |}.

  #[global] Instance MonadState__WFST : MonadState S (WFST S) :=
    {| get := getWFST ;
       put := putWFST |}.

  (* Monad laws not proven. Not using [SProp]. *)

End WFST.

Program Definition obsWFST (S R : Type) (m : state S R) : WFST S R :=
  fun s0 pre r s => runState m s0 = (r, s) /\ pre.

Program Definition VerifyWF {S R}
  (w : WFST S R) (m : state S R)
  (obs: forall {R}, state S R -> WFST S R) : Prop :=
  forall s0 pre r s,
    w s0 pre r s -> obs m s0 pre r s.

#[local] Hint Unfold retWFST bindWFST getWFST putWFST VerifyWF : mst.

Section Dijkstra.

  Variables S A R : Type.

  Theorem Verify_ret_WF : forall (r : R),
      @VerifyWF S _ (ret r) (ret r) (@obsWFST S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_bind_WF : forall m1 m2 k1 k2,
      @VerifyWF S A m1 m2 (@obsWFST S) ->
      (forall a, @VerifyWF S R (k1 a) (k2 a) (@obsWFST S)) ->
      @VerifyWF S R (m1 >>= k1) (m2 >>= k2) (@obsWFST S).
  Proof.
    autounfold with mst.
    sauto lq: on db: mst.
  Qed.

  Theorem Verify_get_WF :
    @VerifyWF S _ get get (@obsWFST S).
  Proof.
    autounfold with mst.
    hauto lq: on.
  Qed.

  Theorem Verify_put_WF : forall (s : S),
    VerifyWF (put s) (put s) (@obsWFST S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.
    
End Dijkstra.

#[export] Hint Resolve
  Verify_ret_WF Verify_bind_WF
  Verify_get_WF Verify_put_WF : mst.

(* But we can prove the following if we use [WFST], which has an additional
   invariant. *)

Program Definition IncorrectWF {R S}
  (presumes : S -> Prop)
  (achieves: S -> R -> S -> Prop)
  (w : WFST S R) : Prop :=
  forall r s, exists s0,
    (presumes s0 -> achieves s0 r s ->
     w s0 (presumes s0) r s) /\
      presumes s0.

Hint Unfold IncorrectWF : mst.

Module ReasoningRules.

  Theorem weaken_pre :
    forall {S R} P P' Q (m : WFST S R),
      IncorrectWF P Q m ->
      (forall (s : S), P s -> P' s) ->
      IncorrectWF P' Q m.
  Proof.
    autounfold with mst. intros. 
    sfirstorder.
  Qed.

  Theorem strengthen_post :
    forall {S R} P Q Q' (m : WFST S R),
      IncorrectWF P Q m ->
      (forall r (s0 s : S), Q' s0 r s -> Q s0 r s) ->
      IncorrectWF P Q' m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.

  Theorem post_disj_intro :
    forall {S R} P Q1 Q2 (m : WFST S R),
    IncorrectWF P Q1 m ->
    IncorrectWF P Q2 m ->
    IncorrectWF P (fun s0 r s => Q1 s0 r s \/ Q2 s0 r s) m.
  Proof.
    autounfold with mst. intros.
    destruct m as [m Hm]; cbn in *.
    specialize (H r s). specialize (H0 r s).
    destruct H as [s1 [? ?]]. destruct H0 as [s2 [? ?]].
    (* This does not seem provable. *)
  Abort.

  Theorem post_disj_elim :
    forall {S R} P Q1 Q2 (m : WFST S R),
    IncorrectWF P (fun s0 r s => Q1 s0 r s \/ Q2 s0 r s) m ->
    IncorrectWF P Q1 m /\
    IncorrectWF P Q2 m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.
    
End ReasoningRules.
  
Module OHearnExample.

    Definition example_3_1_ST : WFST (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else put (x, y, 42).

    Definition example_3_1_state : state (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else put (x, y, 42).

    (* The new incorrectness reasoning that relates [presumes] and [achieves]
       with specification monad, but not effect observations yet! *)
    Theorem example_3_1_incorrect :
      IncorrectWF
        (fun '(x, y, z) => z = 11)
        (fun _ _ '(x, y, z) => z = 42 /\
                              Nat.even x = true /\
                              negb (Nat.even y) = true)
        example_3_1_ST.
    Proof.
      autounfold with mst. cbn; intros.
      destruct s as [[? ?] ?].
      exists (n, n0, 11). split; auto; intros.
      exists (n, n0, 11).
      destruct (Nat.even n) eqn:Hn; cbn; [| sauto q: on].
      destruct (Nat.even n0) eqn:Hn0; cbn; [hauto |].
      hauto.
    Qed.

    (* This is the old thing with Dijkstra monads. *)
    Theorem example_3_1_dijkstra :
      VerifyWF example_3_1_ST example_3_1_state (@obsWFST _).
    Proof.
      unfold example_3_1_ST, example_3_1_state.
      apply Verify_bind_WF; [ apply Verify_get_WF | ].
      intros [[? ?] ?].
      destruct (Nat.even n) eqn:Hn; [ | apply Verify_put_WF ].
      destruct (Nat.even n0) eqn:Hn0; cbn.
      - apply Verify_ret_WF.
      - apply Verify_put_WF.
    Qed.
    
    (* This is the final theorem we want that relates [assumes] and [achieves]
       with effect observation. We only need to compose the above two proofs to
       obtain this. *)
    Theorem example_3_1_final :
      forall x' y' z',
        z' = 42 ->
        Nat.even x' = true ->
        negb (Nat.even y') = true ->
      exists x y z, runState example_3_1_state (x, y, z) = (tt, (x', y', z')).
    Proof.
      pose proof (example_3_1_incorrect) as HI.
      pose proof (example_3_1_dijkstra)  as HV.
      intros. specialize (HI tt (x', y', z')).
      destruct HI as [[[x y] z] [? ?]]. exists x, y, z.
      eapply HV. apply H2; hauto.
    Qed.

End OHearnExample.
