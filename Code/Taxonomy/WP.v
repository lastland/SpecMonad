From Coq Require Import List.
From ExtLib Require Import
  Monad MonadTrans MonadState MonadExc
  StateMonad OptionMonad List.          
From Hammer Require Import Tactics.

Section PureWP.

  Definition PureWP A := (A -> Prop) -> Prop.

  #[local]
    Definition retS {A} (a : A) : PureWP A :=
    fun p => p a.

  #[local]
    Definition bindS {A B}
    (m : PureWP A) (k : A -> PureWP B) : PureWP B :=
    fun p => m (fun a => k a p).

  #[global]
    Instance Monad_PureWP : Monad PureWP :=
    {| ret := fun _ => retS ;
       bind := fun _ _ => bindS |}.

End PureWP.

Section ProgWP.

  Variable S : Type.

  Definition ProgWP := stateT S (optionT PureWP).

  (* Copy-pasted from [Prog.v]. *)
  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : ProgWP A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B}
    (m : ProgWP A) (k : A -> ProgWP B) : ProgWP B :=
    @bind (stateT _ _) _ _ _ m k.  

  #[global]
    Instance Monad__ProgWP : Monad ProgWP :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : ProgWP S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : ProgWP unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__ProgWP : MonadState S ProgWP :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : ProgWP A :=
    @raise _ (stateT _ _) _ _ tt. 
  
  Definition catchP {A}
    (m : ProgWP A) (c : unit -> ProgWP A) : ProgWP A :=
    @catch _ (stateT _ _) _ _ m c.
    
  #[global]
    Instance MonadExc__ProgWP : MonadExc unit ProgWP :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End ProgWP.
