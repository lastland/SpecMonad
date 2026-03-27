From Coq Require Import List.
From ExtLib Require Import
  Monad MonadTrans MonadState MonadExc
  StateMonad OptionMonad List.          
From Hammer Require Import Tactics.

Section PureSpec.

  Definition PureSpec A := (A -> Prop) -> Prop.

  #[local]
    Definition retS {A} (a : A) : PureSpec A :=
    fun p => p a.

  #[local]
    Definition bindS {A B}
    (m : PureSpec A) (k : A -> PureSpec B) : PureSpec B :=
    fun p => m (fun a => k a p).

  #[global]
    Instance Monad_PureSpec : Monad PureSpec :=
    {| ret := fun _ => retS ;
       bind := fun _ _ => bindS |}.

End PureSpec.

Section ProgSpec.

  Variable S : Type.

  Definition ProgSpec := stateT S (optionT PureSpec).

  (* Copy-pasted from [Prog.v]. *)
  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : ProgSpec A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B}
    (m : ProgSpec A) (k : A -> ProgSpec B) : ProgSpec B :=
    @bind (stateT _ _) _ _ _ m k.  

  #[global]
    Instance Monad__ProgSpec : Monad ProgSpec :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : ProgSpec S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : ProgSpec unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__ProgSpec : MonadState S ProgSpec :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : ProgSpec A :=
    @raise _ (stateT _ _) _ _ tt. 
  
  Definition catchP {A}
    (m : ProgSpec A) (c : unit -> ProgSpec A) : ProgSpec A :=
    @catch _ (stateT _ _) _ _ m c.
    
  #[global]
    Instance MonadExc__ProgSpec : MonadExc unit ProgSpec :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End ProgSpec.
