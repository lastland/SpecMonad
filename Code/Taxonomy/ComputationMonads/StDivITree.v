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
(** * Facts and laws (merged from ProgFacts.v)                          *)
(* ================================================================= *)

(** * Monad law proofs for [stdivitree] and its transformer stack.

    We prove [MonadLawsE] (ITree's monad laws up to [Eq1] equivalence)
    generically for ExtLib's [optionT] and [stateT], then assemble
    the instance for [stdivitree S = stateT S (optionT (itree void1))].

    The base equality on [itree void1] is [eutt eq] (equivalence up
    to taus), provided by [Eq1_ITree] from the ITree library.  This
    lifts through [optionT] and [stateT] via the generic instances
    defined here. *)

From Coq Require Import Morphisms RelationClasses.
From ITree Require Import ITree Basics.Monad Core.ITreeMonad.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.


(* ================================================================= *)
(** ** Generic [Eq1] and [MonadLawsE] for ExtLib's [optionT]         *)
(* ================================================================= *)

Section OptionT.

  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {MLM : @MonadLawsE M Eq1M MonadM}.

  (** Two [optionT M A] values are equivalent when their
      underlying [M (option A)] values are [eq1]-equivalent.
      For [M = itree void1] this is [eutt eq] at type [option A]. *)
  #[global]
  Instance Eq1_optionT : Eq1 (optionT M) :=
    fun A x y => eq1 (unOptionT x) (unOptionT y).

  #[global]
  Instance Eq1Equivalence_optionT
    : @Eq1Equivalence (optionT M) _ Eq1_optionT.
  Proof.
    constructor;
      repeat intro; unfold eq1, Eq1_optionT in *.
    - reflexivity.
    - symmetry; auto.
    - etransitivity; eauto.
  Qed.

  #[global]
  Instance MonadLawsE_optionT
    : @MonadLawsE (optionT M) Eq1_optionT _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros T U f x. unfold eq1, Eq1_optionT. cbn.
      rewrite bind_ret_l.
      destruct (f x); reflexivity.
    - (* bind_ret_r *)
      intros T x. unfold eq1, Eq1_optionT. cbn.
      transitivity (bind (unOptionT x) (fun y => ret y)).
      + apply Proper_bind. reflexivity.
        repeat red; intros. destruct a; reflexivity.
      + apply bind_ret_r.
    - (* bind_bind *)
      intros T U V x f g. unfold eq1, Eq1_optionT. cbn.
      rewrite bind_bind.
      apply Proper_bind. reflexivity.
      intros. repeat red. destruct a.
      + reflexivity.
      + rewrite bind_ret_l. reflexivity.
    - (* Proper_bind *)
      repeat intro. unfold eq1, Eq1_optionT in *. cbn.
      apply Proper_bind.
      + exact H.
      + repeat red. intros. destruct a.
        * apply H0.
        * reflexivity.
  Qed.

End OptionT.

(* ================================================================= *)
(** ** Generic [Eq1] and [MonadLawsE] for ExtLib's [stateT]          *)
(* ================================================================= *)

Section StateT.

  Variable St : Type.
  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {MLM : @MonadLawsE M Eq1M MonadM}.

  #[local] Existing Instance Monad_stateT.

  (** Two [stateT St M A] values are equivalent when, for every
      initial state [s], their underlying [M (A * St)] values are
      [eq1]-equivalent.  For the full [stdivitree] stack this unfolds to
      [forall s, eutt eq (... s) (... s)]. *)
  #[global]
  Instance Eq1_stateT : Eq1 (stateT St M) :=
    fun T x y => forall s, eq1 (runStateT x s) (runStateT y s).

  #[global]
  Instance Eq1Equivalence_stateT
    : @Eq1Equivalence (stateT St M) _ Eq1_stateT.
  Proof.
    constructor.
    - repeat intro; unfold eq1, Eq1_stateT in *.
      reflexivity.
    - repeat intro; unfold eq1, Eq1_stateT in *.
      symmetry. apply H.
    - repeat intro; unfold eq1, Eq1_stateT in *.
      etransitivity.
      + apply H.
      + apply H0.
  Qed.

  #[global]
  Instance MonadLawsE_stateT
    : @MonadLawsE (stateT St M) Eq1_stateT _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros T U f x s. cbn.
      rewrite bind_ret_l. reflexivity.
    - (* bind_ret_r *)
      intros T x s. cbn.
      transitivity (bind (runStateT x s) (fun y => ret y)).
      + apply Proper_bind. reflexivity.
        repeat red; intros. destruct a; reflexivity.
      + apply bind_ret_r.
    - (* bind_bind *)
      intros T U V x f g s. cbn.
      rewrite bind_bind.
      apply Proper_bind. reflexivity.
      repeat red; intros. destruct a. reflexivity.
    - (* Proper_bind *)
      repeat intro. cbn.
      apply Proper_bind.
      + apply H.
      + repeat red. intros. destruct a.
        apply H0.
  Qed.

End StateT.

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
