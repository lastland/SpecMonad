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

From ITree Require Import Basics.Monad Core.ITreeMonad.
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

From ITree Require Import Eq.

(* ================================================================= *)
(** ** Outcome kernel for arrow-derived SP observations              *)
(* ================================================================= *)

Section OutcomeKernel.

  Variable S : Type.

  Definition outcomes {A} (m : stdivitree S A) (s : S) (r : option (A * S)) : Prop :=
    eutt eq (unOptionT (runStateT m s)) (Ret r).

  Lemma outcomes_ret {A} (a : A) (s : S) (r : option (A * S)) :
    outcomes (retP S a) s r <-> r = Some (a, s).
  Proof.
    unfold outcomes, retP. cbn.
    split.
    - intro H. apply eutt_inv_Ret in H. congruence.
    - intro H. rewrite H. reflexivity.
  Qed.

  Lemma outcomes_bind {A B} (m : stdivitree S A) (k : A -> stdivitree S B)
    (s : S) (r : option (B * S)) :
    outcomes (bindP S m k) s r <->
    exists oa, outcomes m s oa /\
      match oa with
      | Some (a, s') => outcomes (k a) s' r
      | None => r = None
      end.
  Proof.
    unfold outcomes, bindP. cbn. split.
    - intro H. apply eutt_inv_bind_ret in H. destruct H as [oy [H1 H2]].
      destruct oy as [[a s']|].
      + exists (Some (a, s')). split; [ exact H1 | exact H2 ].
      + exists None. split; [ exact H1 |].
        apply eutt_inv_Ret in H2. congruence.
    - intros [oy [H1 H2]].
      rewrite H1.
      destruct oy as [[a s']|].
      + etransitivity.
        * apply (eq_sub_eutt eq), ITree.Eq.Eqit.bind_ret_l.
        * exact H2.
      + rewrite H2.
        etransitivity.
        * apply (eq_sub_eutt eq), ITree.Eq.Eqit.bind_ret_l.
        * reflexivity.
  Qed.

End OutcomeKernel.
