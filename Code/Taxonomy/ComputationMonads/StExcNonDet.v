From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.

Section SetM.

  Definition SetM A := A -> Prop.

  #[global]
    Instance Monad_SetM : Monad SetM :=
    {| ret := fun _ a => fun x => x = a ;
       bind := fun _ _ m k => fun b => exists a, m a /\ k a b |}.

End SetM.

Section StExcNonDet.

  Variable S : Type.

  Definition stexcnd A := stateT S (optionT SetM) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : stexcnd A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : stexcnd A) (k : A -> stexcnd B) : stexcnd B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__stexcnd : Monad stexcnd :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : stexcnd S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : stexcnd unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__stexcnd : MonadState S stexcnd :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : stexcnd A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : stexcnd A) (c : unit -> stexcnd A) : stexcnd A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__stexcnd : MonadExc unit stexcnd :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

  Definition orP {A} (m1 m2 : stexcnd A) : stexcnd A :=
    mkStateT (fun s =>
      @mkOptionT SetM _ (fun oa =>
        unOptionT (runStateT m1 s) oa \/
        unOptionT (runStateT m2 s) oa)).

End StExcNonDet.

(* ================================================================= *)
(** * Facts and laws (merged from NonDetProgFacts.v)                          *)
(* ================================================================= *)

(** * Monad law proofs for [SetM] and [stexcnd].

    [SetM A = A -> Prop] is the powerset/nondeterminism monad.
    Monad laws hold up to Leibniz equality via propositional and
    functional extensionality.

    [stexcnd S = stateT S (optionT SetM)] then inherits
    [MonadLawsE] via the generic [optionT] and [stateT] instances
    from [Prog]. *)

From Coq Require Import FunctionalExtensionality PropExtensionality.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [SetM]                             *)
(* ================================================================= *)

Section SetM.

  #[global]
  Instance Eq1_SetM : Eq1 SetM :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_SetM
    : @Eq1Equivalence SetM _ Eq1_SetM.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_SetM
    : @MonadLawsE SetM Eq1_SetM _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro c.
      apply propositional_extensionality. sauto.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_SetM in *. subst.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split; intros [a [Ha Hk]]; exists a; split; try exact Ha;
        [rewrite <- (Hfg a) | rewrite (Hfg a)]; exact Hk.
  Qed.

End SetM.

(* ================================================================= *)
(** ** [MonadLawsE] for [stexcnd S]                                    *)
(* ================================================================= *)

Section StExcNonDet.

  Variable S : Type.

  Definition Eq1__stexcnd : Eq1 (stexcnd S) :=
    Eq1_stateT S (optionT SetM).

  Definition MonadLawsE__stexcnd
    : @MonadLawsE (stexcnd S) _ (Monad__stexcnd S) :=
    MonadLawsE_stateT S (optionT SetM).

End StExcNonDet.
