(** * Monad law proofs for [PureSpec] and [ProgSpec].

    [PureSpec A = (A -> Prop) -> Prop] is a continuation monad whose
    laws hold definitionally (by eta-reduction).  Only [Proper_bind]
    requires functional extensionality.

    [ProgSpec S = stateT S (optionT PureSpec)] then inherits
    [MonadLawsE] via the generic [optionT] and [stateT] instances
    from [ProgFacts]. *)

From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness Require Import
  Taxonomy.Spec
  Taxonomy.ProgFacts.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [PureSpec]                         *)
(* ================================================================= *)

Section PureSpecFacts.

  #[global]
  Instance Eq1_PureSpec : Eq1 PureSpec :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_PureSpec
    : @Eq1Equivalence PureSpec _ Eq1_PureSpec.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_PureSpec
    : @MonadLawsE PureSpec Eq1_PureSpec _.
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
      unfold eq1, Eq1_PureSpec in *.
      subst.
      apply functional_extensionality; intro p.
      cbn. f_equal.
      apply functional_extensionality; intro a.
      specialize (Hfg a).
      unfold eq1, Eq1_PureSpec in Hfg.
      rewrite Hfg. reflexivity.
  Qed.

End PureSpecFacts.

(* ================================================================= *)
(** ** [MonadLawsE] for [ProgSpec S]                                  *)
(* ================================================================= *)

Section ProgSpecFacts.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_PureSpec]  (Leibniz eq)
      → [Eq1_optionT]   (eq on unwrapped PureSpec)
      → [Eq1_stateT]    (pointwise eq)

      and similarly for [MonadLawsE]. *)

  Definition Eq1__ProgSpec : Eq1 (ProgSpec S) :=
    Eq1_stateT S (optionT PureSpec).

  Definition MonadLawsE__ProgSpec
    : @MonadLawsE (ProgSpec S) _ (Monad__ProgSpec S) :=
    MonadLawsE_stateT S (optionT PureSpec).

End ProgSpecFacts.
