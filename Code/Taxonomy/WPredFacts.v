(** * Monad law proofs for [WPred] and [ProgWPred].

    [WPred A = A -> Prop] is the powerset/nondeterminism monad (identical
    in structure to [SetM]).  Monad laws hold up to Leibniz equality via
    propositional and functional extensionality.

    [ProgWPred S = stateT S (optionT WPred)] then inherits [MonadLawsE]
    via the generic [optionT] and [stateT] instances from [ProgFacts].
    Unfolded, [ProgWPred S A = S -> option (A * S) -> Prop]. *)

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
  Taxonomy.WPred
  Taxonomy.ProgFacts.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [WPred]                            *)
(* ================================================================= *)

Section WPredFacts.

  #[global]
  Instance Eq1_WPred : Eq1 WPred :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_WPred
    : @Eq1Equivalence WPred _ Eq1_WPred.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_WPred
    : @MonadLawsE WPred Eq1_WPred _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_WPred. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_WPred. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_WPred. cbn.
      apply functional_extensionality; intro c.
      apply propositional_extensionality. sauto.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_WPred in *. subst.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split; intros [a [Ha Hk]]; exists a; split; try exact Ha;
        [rewrite <- (Hfg a) | rewrite (Hfg a)]; exact Hk.
  Qed.

End WPredFacts.

(* ================================================================= *)
(** ** [MonadLawsE] for [ProgWPred S]                                *)
(* ================================================================= *)

Section ProgWPredFacts.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_WPred]   (Leibniz eq)
      → [Eq1_optionT]   (eq on unwrapped WPred)
      → [Eq1_stateT]    (pointwise eq)

      and similarly for [MonadLawsE]. *)

  Definition Eq1__ProgWPred : Eq1 (ProgWPred S) :=
    Eq1_stateT S (optionT WPred).

  Definition MonadLawsE__ProgWPred
    : @MonadLawsE (ProgWPred S) _ (Monad__ProgWPred S) :=
    MonadLawsE_stateT S (optionT WPred).

End ProgWPredFacts.
