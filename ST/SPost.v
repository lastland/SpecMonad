From ExtLib Require Import Monad.
From Hammer Require Import Tactics.

Definition SPost (A : Type) := forall (pre : Prop), A -> {p : Prop | p -> pre}.

Section SPost.

  Program Definition retSPost {A} (a : A) : SPost A :=
    fun pre r => pre /\ r = a.

  Program Definition bindSPost {A B} (m : SPost A) (k : A -> SPost B) : SPost B :=
    fun pre b => exists a, k a (m pre a) b.
  Next Obligation. sfirstorder. Qed.

  Instance Monad__SPost : Monad SPost :=
    {| ret := fun _ => retSPost ;
       bind := fun _ _ => bindSPost |}.
End SPost.

