(** * Monad law proofs for [SetM] and [ndprog].

    [SetM A = A -> Prop] is the powerset/nondeterminism monad.
    Monad laws hold up to Leibniz equality via propositional and
    functional extensionality.

    [ndprog S = stateT S (optionT SetM)] then inherits
    [MonadLawsE] via the generic [optionT] and [stateT] instances
    from [ProgFacts]. *)

From Coq Require Import
  FunctionalExtensionality
  PropExtensionality
  Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness Require Import
  Taxonomy.NonDetProg
  Taxonomy.ProgFacts.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [SetM]                             *)
(* ================================================================= *)

Section SetMFacts.

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

End SetMFacts.

(* ================================================================= *)
(** ** [MonadLawsE] for [ndprog S]                                    *)
(* ================================================================= *)

Section NonDetProgFacts.

  Variable S : Type.

  Definition Eq1__ndprog : Eq1 (ndprog S) :=
    Eq1_stateT S (optionT SetM).

  Definition MonadLawsE__ndprog
    : @MonadLawsE (ndprog S) _ (Monad__ndprog S) :=
    MonadLawsE_stateT S (optionT SetM).

End NonDetProgFacts.
