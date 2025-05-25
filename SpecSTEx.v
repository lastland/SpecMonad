From ExtLib Require Import Monad MonadState.
From Hammer Require Import Hammer Tactics.

Definition conj2 {A B} (p1 p2 : A -> B -> Prop) : A -> B -> Prop :=
  fun a b => p1 a b /\ p2 a b.

Definition disj2 {A B} (p1 p2 : A -> B -> Prop) : A -> B -> Prop :=
  fun a b => p1 a b \/ p2 a b.

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

  Definition fail {R} (e : E) : SpecSTEx R :=
    fun _ q => q e. 

End SpecSTEx.


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

  #[local] Hint Unfold getST putST bindST : specst.

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
  
End Examples.
