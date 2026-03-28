From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.

Section SetM.

  Definition SetM A := A -> Prop.

  #[global]
    Instance Monad_SetM : Monad SetM :=
    {| ret := fun _ a => fun x => x = a ;
       bind := fun _ _ m k => fun b => exists a, m a /\ k a b |}.

End SetM.

Section NonDetProg.

  Variable S : Type.

  Definition ndprog A := stateT S (optionT SetM) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : ndprog A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : ndprog A) (k : A -> ndprog B) : ndprog B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__ndprog : Monad ndprog :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : ndprog S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : ndprog unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__ndprog : MonadState S ndprog :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : ndprog A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : ndprog A) (c : unit -> ndprog A) : ndprog A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__ndprog : MonadExc unit ndprog :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

  Definition orP {A} (m1 m2 : ndprog A) : ndprog A :=
    mkStateT (fun s =>
      @mkOptionT SetM _ (fun oa =>
        unOptionT (runStateT m1 s) oa \/
        unOptionT (runStateT m2 s) oa)).

End NonDetProg.
