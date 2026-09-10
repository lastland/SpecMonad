From ITree Require Import ITree.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.

Section StDivITree.

  Variable S : Type.

  Definition stdivitree A := stateT S (optionT (itree void1)) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : stdivitree A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : stdivitree A) (k : A -> stdivitree B) : stdivitree B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__stdivitree : Monad stdivitree :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : stdivitree S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : stdivitree unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__stdivitree : MonadState S stdivitree :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : stdivitree A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : stdivitree A) (c : unit -> stdivitree A) : stdivitree A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__stdivitree : MonadExc unit stdivitree :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End StDivITree.

(* ================================================================= *)
(** * Facts and laws                                                  *)
(* ================================================================= *)

(** The generic [optionT] / [stateT] / [readerT] law instances this assembles
    from live in [TransformerLaws.v].  The base equality on [itree void1] is
    [eutt eq], provided by [Eq1_ITree]; it lifts through [optionT] and
    [stateT] via those generic instances. *)

From Coq Require Import Morphisms RelationClasses.
From ITree Require Import ITree Basics.Monad Core.ITreeMonad.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

(* ================================================================= *)
(** ** [MonadLawsE] for [stdivitree S]                                     *)
(* ================================================================= *)

Section Prog.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_ITree]  (eutt eq)
      → [Eq1_optionT]  (eutt eq on unwrapped itree)
      → [Eq1_stateT]   (pointwise eutt eq)

      and similarly for [MonadLawsE]. *)

  #[local] Existing Instance Eq1_ITree.
  #[local] Existing Instance Eq1Equivalence_ITree.
  #[local] Existing Instance MonadLawsE_ITree.

  Definition Eq1__stdivitree : Eq1 (stdivitree S) := Eq1_stateT S (optionT (itree void1)).

  Definition MonadLawsE__stdivitree : @MonadLawsE (stdivitree S) _ (Monad__stdivitree S) :=
    MonadLawsE_stateT S (optionT (itree void1)).

End Prog.
