From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.STExamples ST.WFST.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S1 S2 A : Type.

  Definition WFSepST := WFST (S1 * S2) A. 

End Types.

Program Definition IncorrectU {R S1 S2}
  (presumes : S1 -> Prop)
  (achieves: R -> S1 -> Prop)
  (w : WFSepST S1 S2 R) : Prop :=
  forall r s1, 
    achieves r s1 ->
    exists s0, forall s0', exists s2, w (s0, s0') (presumes s0) r (s1, s2) /\ presumes s0.

Hint Unfold IncorrectU : mst.

Module OHearnExample.

    Definition example_3_1_ST : WFSepST nat (nat * nat) unit :=
      '(z, (x, y)) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (42, (x, y)) else ret tt
        else put (42, (x, y)).

    Definition example_3_1_state : state (nat * (nat * nat)) unit :=
      '(z, (x, y)) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (42, (x, y)) else ret tt
        else put (42, (x, y)).

    (* The new incorrectness reasoning that relates [presumes] and [achieves]
       with specification monad, but not effect observations yet! *)
    Theorem example_3_1_incorrect :
      IncorrectU
        (fun z => z = 11)
        (fun _ z => z = 42)
        example_3_1_ST.
    Proof.
      autounfold with mst. cbn; intros.
      exists 11. intros [x y]. exists (x, y). split; auto; cbn.
      assert ((exists (y0 : nat * nat) (a : nat) (s' : nat * (nat * nat)),
                 proj1_sig
                   (proj1_sig
                      (let (x0, y1) := y0 in
                       if Nat.even x0
                       then if negb (Nat.even y1) then putWFST (42, (x0, y1)) else retWFST (nat * (nat * nat)) tt
                       else putWFST (42, (x0, y1))) s' (11 = 11 /\ (a, y0) = (11, (x, y)) /\ s' = (11, (x, y)))) r (
                     s1, (x, y))) ->
              exists a s' : nat * (nat * nat),
                proj1_sig
                  (proj1_sig
                     (let (_, y0) := a in
                      let (x0, y1) := y0 in
                      if Nat.even x0
                      then if negb (Nat.even y1) then putWFST (42, (x0, y1)) else retWFST (nat * (nat * nat)) tt
                      else putWFST (42, (x0, y1))) s' (11 = 11 /\ a = (11, (x, y)) /\ s' = (11, (x, y)))) r (
                    s1, (x, y))).
      { intros. destruct H0 as [y0 [a ?]].
        exists (a, y0). apply H0. }
      apply H0. exists (x, y).
      destruct (Nat.even x) eqn:Hx; cbn.
      - destruct (Nat.even y) eqn:Hy; cbn.
        + 
      - hauto lq: on.

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
      intros. specialize (HI tt (x', y', z') ltac:(hauto lq: on)). 
      destruct HI as [[[x y] z] [HI ?]]. exists x, y, z.
      eapply HV. apply HI.
    Qed.

End OHearnExample.
