From ExtLib Require Import Monad MonadState.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Export Common.Common.

Section SpecSTEx.
  Variable S E : Type.
  
  Definition SpecSTEx (R : Type) :=
    (R -> S -> Prop) -> (E -> S -> Prop) -> S -> Prop.

  Definition retST {R} (r : R) : SpecSTEx R :=
    fun p _ => p r.

  Definition bindST {X Y}
    (m : SpecSTEx X)
    (k : X -> SpecSTEx Y) : SpecSTEx Y :=
    fun p e => m (fun x => k x p e) e.

  Definition getST : SpecSTEx S :=
    fun p _ s => p s s.

  Definition putST (s : S) : SpecSTEx unit :=
    fun p _ _ => p tt s.

  Definition fail_ {R} (e : E) : SpecSTEx R :=
    fun _ q => q e. 

End SpecSTEx.

Arguments fail_ {S} {E} {R}.


#[global] Instance Monad__SpecST {S E} : Monad (SpecSTEx S E) :=
  {| bind := @bindST S E ;
     ret  := @retST S E
  |}.

#[global] Instance MonadState__SpecST {S E} : MonadState S (SpecSTEx S E) :=
  {| get := @getST S E ;
     put := @putST S E
  |}.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Section Examples.

  Local Open Scope monad_scope.
  Local Open Scope nat_scope.
  Import MonadNotation.

  #[local] Hint Unfold getST putST bindST fail_ : specst.

  Definition read_inc_write : SpecSTEx nat unit unit :=
    x <- get ;; put (x + 1).

  Theorem read_inc_write_spec {E} :
    forall s, s >= 0 -> read_inc_write (fun _ s => s >= 1) E s.
  Proof.
    intros. unfold read_inc_write. cbn.
    autounfold with specst. lia.
  Qed.

  Definition read_if_inc_write : SpecSTEx nat unit unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Theorem read_if_inc_write_spec {E} :
    forall s, read_if_inc_write (fun _ s => s >= 43 \/ s = 0) E s.
  Proof.
    intros. unfold read_if_inc_write.
    simpl. autounfold with specst.
    pose proof (Nat.leb_spec0 42 s) as Hs.
    inversion Hs; simpl; lia.
  Qed.

  Definition read_if_inc_write_else_fail : SpecSTEx nat nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else fail_ 0.

  Theorem read_if_inc_write_else_fail_spec :
    forall s, read_if_inc_write_else_fail
           (fun _ s => s >= 43)
           (fun n _ => n = 0)
           s.
  Proof.
    intros. unfold read_if_inc_write_else_fail.
    simpl. autounfold with specst.
    pose proof (Nat.leb_spec0 42 s) as Hs.
    inversion Hs; simpl; lia.
  Qed.

End Examples.
