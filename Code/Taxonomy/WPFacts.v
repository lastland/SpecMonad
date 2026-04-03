(** * Monad law proofs for [PureWP] and [ProgWP].

    [PureWP A = (A -> Prop) -> Prop] is a continuation monad whose
    laws hold definitionally (by eta-reduction).  Only [Proper_bind]
    requires functional extensionality.

    [ProgWP S = stateT S (optionT PureWP)] then inherits
    [MonadLawsE] via the generic [optionT] and [stateT] instances
    from [ProgFacts]. *)

From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness Require Import
  Taxonomy.WP
  Taxonomy.ProgFacts.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [PureWP]                         *)
(* ================================================================= *)

Section PureWPFacts.

  #[global]
  Instance Eq1_PureWP : Eq1 PureWP :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_PureWP
    : @Eq1Equivalence PureWP _ Eq1_PureWP.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_PureWP
    : @MonadLawsE PureWP Eq1_PureWP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x.
      reflexivity.
    - (* bind_ret_r *)
      intros A x.
      reflexivity.
    - (* bind_bind *)
      intros A B C x f g.
      reflexivity.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg.
      unfold eq1, Eq1_PureWP in *.
      subst.
      apply functional_extensionality; intro p.
      cbn. f_equal.
      apply functional_extensionality; intro a.
      specialize (Hfg a).
      unfold eq1, Eq1_PureWP in Hfg.
      rewrite Hfg. reflexivity.
  Qed.

End PureWPFacts.

(* ================================================================= *)
(** ** [MonadLawsE] for [ProgWP S]                                  *)
(* ================================================================= *)

Section ProgWPFacts.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_PureWP]  (Leibniz eq)
      → [Eq1_optionT]   (eq on unwrapped PureWP)
      → [Eq1_stateT]    (pointwise eq)

      and similarly for [MonadLawsE]. *)

  Definition Eq1__ProgWP : Eq1 (ProgWP S) :=
    Eq1_stateT S (optionT PureWP).

  Definition MonadLawsE__ProgWP
    : @MonadLawsE (ProgWP S) _ (Monad__ProgWP S) :=
    MonadLawsE_stateT S (optionT PureWP).

End ProgWPFacts.
