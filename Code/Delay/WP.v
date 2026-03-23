From ExtLib Require Import
  Monad MonadTrans MonadLaws
  StateMonad OptionMonad
  MonadState MonadExc.
From ITree Require Import ITree Eq.
From ITree.Extra.Dijkstra Require Import DelaySpecMonad.

#[local] Open Scope itree_scope.

Section Prog.

  Variable S : Type.

  (** A program is stateful, can have exceptions, and is nondeterministic. *)
  Definition prog A := stateT S (optionT Delay) A -> Prop.

  Definition eutt_SOD {A} (a b: stateT S (optionT Delay) A) : Prop :=
    match a, b with
    | mkStateT f, mkStateT g =>
        forall s, match f s, g s with
             | mkOptionT x, mkOptionT y =>
                 eutt eq x y
             end
    end.

  Definition ret_prog {A} (a : A) : prog A :=
    fun p => eutt_SOD p (lift (ret a)).
    
  Definition bind_prog {A B} (m : prog A) (k : A -> prog B) : prog B :=
    fun b => exists a, m (lift (ret a)) /\ k a b.

  Instance Monad__prog : Monad prog :=
    {| ret := fun A => @ret_prog A ;
       bind := fun A B => @bind_prog A B
    |}.

  Definition get_prog : prog S :=
    fun p => eutt_SOD p get.

  Definition put_prog (s : S) : prog unit :=
    fun p => eutt_SOD p (put s).

  Instance MonadState__prog : MonadState S prog :=
    {| get := get_prog ;
       put := put_prog
    |}.


  
End Prog.

Section ProgLaws.
