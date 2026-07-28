From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness Require Import Taxonomy.NonDetProg.

(** [WPred] is a transparent alias for the powerset/nondeterminism
    monad [SetM := A -> Prop] defined in [NonDetProg].  Its monad,
    [Eq1], and [MonadLawsE] laws are bridged to [SetM]'s (proved in
    [NonDetProgFacts]); none are reproved here. *)

Definition WPred : Type -> Type := SetM.

#[global] Instance Monad_WPred : Monad WPred := Monad_SetM.

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
