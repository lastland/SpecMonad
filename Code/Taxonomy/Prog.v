From Coq Require Import List.
From ITree Require Import ITree.
From ExtLib Require Import
  Monad MonadTrans MonadState MonadExc
  StateMonad OptionMonad List.          
From Hammer Require Import Tactics.

Import ListNotations.
#[local] Open Scope list_scope.

Section Prog.

  Variable S : Type.

  Definition prog A := stateT S (optionT (itree void1)) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : prog A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : prog A) (k : A -> prog B) : prog B :=
    @bind (stateT _ _) _ _ _ m k.  

  #[global]
    Instance Monad__prog : Monad prog :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : prog S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : prog unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__prog : MonadState S prog :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : prog A :=
    @raise _ (stateT _ _) _ _ tt. 
  
  Definition catchP {A} (m : prog A) (c : unit -> prog A) : prog A :=
    @catch _ (stateT _ _) _ _ m c.
    
  #[global]
    Instance MonadExc__prog : MonadExc unit prog :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End Prog.
