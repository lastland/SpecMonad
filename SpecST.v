From ExtLib Require Import Monad MonadState.
From Hammer Require Import Hammer Tactics.

Definition conj2 {A B} (p1 p2 : A -> B -> Prop) : A -> B -> Prop :=
  fun a b => p1 a b /\ p2 a b.

Definition disj2 {A B} (p1 p2 : A -> B -> Prop) : A -> B -> Prop :=
  fun a b => p1 a b \/ p2 a b.

Section SpecST.
  Variable S : Type.
  
  Definition SpecST (R : Type) :=
    { m : (R -> S -> Prop) -> S -> Prop |
      (forall (p q : R -> S -> Prop) s,
        (forall r s, p r s -> q r s) -> m p s -> m q s)
    }.

  Program Definition retST {R} (r : R) : SpecST R :=
    fun p => p r.

  Program Definition bindST {X Y}
    (m : SpecST X)
    (k : X -> SpecST Y) : SpecST Y :=
    fun p => m (fun x => k x p).
  Next Obligation.
  destruct m as [m Hm]. cbn in *.
  eapply Hm; [| apply H0]. sauto.
  Defined.

  Program Definition getST : SpecST S :=
    fun p s => p s s.

  Program Definition putST (s : S) : SpecST unit :=
    fun p _ => p tt s.

End SpecST.


#[global] Instance Monad__SpecST {S} : Monad (SpecST S) :=
  {| bind := @bindST S ;
     ret  := @retST S
  |}.

#[global] Instance MonadState__SpecST {S} : MonadState S (SpecST S) :=
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

  Definition read_inc_write : SpecST nat unit :=
    x <- get ;; put (x + 1).

  Theorem read_inc_write_spec :
    forall s, s >= 0 -> proj1_sig read_inc_write (fun _ s => s >= 1) s.
  Proof.
    intros. unfold read_inc_write. cbn.
    autounfold with specst. lia.
  Qed.

  Definition read_if_inc_write : SpecST nat unit :=
    x <- get ;; if (42 <=? x) then put (x + 1) else put 0.

  Theorem read_if_inc_write_spec :
    forall s, proj1_sig read_if_inc_write (fun _ s => s >= 43 \/ s = 0) s.
  Proof.
    intros. unfold read_if_inc_write.
    simpl. autounfold with specst.
    pose proof (Nat.leb_spec0 42 s) as Hs.
    inversion Hs; simpl; lia.
  Qed.
  
End Examples.
