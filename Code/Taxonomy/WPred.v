From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.

Section WPred.

  Definition WPred A := A -> Prop.

  #[local]
    Definition retS {A} (a : A) : WPred A :=
    fun a' => a = a'.

  #[local]
    Definition bindS {A B}
    (m : WPred A) (k : A -> WPred B) : WPred B :=
    fun b' => exists a', m a' /\ k a' b'.

  #[global]
    Instance Monad_WPred : Monad WPred :=
    {| ret := fun _ => retS ;
       bind := fun _ _ => bindS |}.

End WPred.

Section ProgWPred.

  Variable S : Type.

  Definition ProgWPred := stateT S (optionT WPred).

  (* Copy-pasted from [Prog.v]. *)
  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : ProgWPred A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B}
    (m : ProgWPred A) (k : A -> ProgWPred B) : ProgWPred B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__ProgWPred : Monad ProgWPred :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : ProgWPred S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : ProgWPred unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__ProgWPred : MonadState S ProgWPred :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : ProgWPred A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A}
    (m : ProgWPred A) (c : unit -> ProgWPred A) : ProgWPred A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__ProgWPred : MonadExc unit ProgWPred :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End ProgWPred.
