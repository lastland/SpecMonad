From ExtLib Require Import Monad MonadState.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Export Common.Common.

Section SpecST.
  Variable S : Type.

  Definition SpecST (R : Type) :=
    (R -> S -> Prop) -> S -> Prop.

  Definition retST {R} (r : R) : SpecST R :=
    fun p => p r.

  Definition bindST {X Y}
    (m : SpecST X)
    (k : X -> SpecST Y) : SpecST Y :=
    fun p => m (fun x => k x p).

  Definition getST : SpecST S :=
    fun p s => p s s.

  Definition putST (s : S) : SpecST unit :=
    fun p _ => p tt s.

End SpecST.


#[export] Instance Monad__SpecST {S} : Monad (SpecST S) :=
  {| bind := @bindST S ;
     ret  := @retST S
  |}.

#[export] Instance MonadState__SpecST {S} : MonadState S (SpecST S) :=
  {| get := @getST S ;
     put := @putST S
  |}.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST : specst.

  Definition read_inc_write_spec : SpecST nat unit :=
    x <- get ;; put (x + 1).

  Theorem read_inc_write_spec_thm :
    forall s, s >= 0 -> read_inc_write_spec (fun _ s => s >= 1) s.
  Proof.
    intros. unfold read_inc_write_spec. cbn.
    autounfold with specst. lia.
  Qed.

  Definition read_if_inc_write_spec : SpecST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Theorem read_if_inc_write_them :
    forall s, read_if_inc_write_spec (fun _ s => s >= 43 \/ s = 0) s.
  Proof.
    intros. unfold read_if_inc_write_spec.
    simpl. autounfold with specst.
    pose proof (Nat.leb_spec0 42 s) as Hs.
    inversion Hs; simpl; lia.
  Qed.
  
End Examples.
