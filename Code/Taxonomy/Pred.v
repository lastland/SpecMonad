(** * The relational strongest-postcondition arrow [Pred] and
      composed spec types.

    [Pred A B := A -> B -> Prop] is a relation from [A] to [B], the
    category of relations interpreted as forward predicate
    transformers (strongest-postcondition arrows).  Using relations as
    the base ensures all arrow laws are provable without requiring
    monotonicity or additivity constraints.

    This file provides the arrow-view instances ([Arrow],
    [ArrowChoice], [ArrowApply], [ArrowLoop]) plus the complementary
    monad view: for every fixed [A], the partially applied type
    [fun B => Pred A B] is a monad in [B] via relational composition.

    With both views available, we expose composed specification types
    for the three computation monads ([prog], [ndprog], [nditprog]) in
    two equivalent styles:

    - Arrow view — applies [stateArrT] and [optionArrT] to [Pred]:

        [progPredArr S A = stateArrT S (optionArrT Pred) unit A]
        [nditPredArr S A = stateArrT S (optionArrT (optionArrT Pred)) unit A]

    - Monad view — applies [stateT] and [optionT] (from ExtLib) to
      [Pred unit] (the unary-in-[B] monad specialization):

        [progPredM S A = stateT S (optionT (Pred unit)) A]
        [nditPredM S A = stateT S (optionT (optionT (Pred unit))) A]

    The monad view inherits [MonadLawsE] automatically via the generic
    [MonadLawsE_optionT] and [MonadLawsE_stateT] instances in
    [Taxonomy/ProgFacts.v].

    This file holds only the definitions and instances.  Their laws
    ([ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws], [ArrowLoopLaws],
    [Eq1Equivalence], [MonadLawsE]) are proved in
    [Taxonomy/PredFacts.v]. *)

From Coq Require Import
  Morphisms RelationClasses.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import
  Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy Require Import ProgFacts.

(* ================================================================= *)
(** ** [Pred]: definition and arrow instances                         *)
(* ================================================================= *)

Definition Pred (A B : Type) : Type := A -> B -> Prop.

(** Pointwise iff is the intrinsic equivalence on relations — no
    extensionality axioms required. *)
Definition Pred_eq {A B} (f g : Pred A B) : Prop :=
  forall a b, f a b <-> g a b.

#[global]
Instance Pred_eq_Equivalence {A B} : Equivalence (@Pred_eq A B).
Proof.
  constructor.
  - intros f a b. reflexivity.
  - intros f g H a b. symmetry. apply H.
  - intros f g h H1 H2 a b. etransitivity; [apply H1 | apply H2].
Qed.

#[global]
Instance ArrowEq_Pred : ArrowEq Pred := {
  arrow_eq := @Pred_eq
}.

(** Covariant inclusion: [R1 ≤ R2] iff [R1 ⊆ R2]. A larger relation
    is "above" a smaller one. This pairs with the partial-correctness
    Hoare order on [PrePost] in [Taxonomy/Galois.v]. *)
Definition Pred_le {A B} (R1 R2 : Pred A B) : Prop :=
  forall a b, R1 a b -> R2 a b.

#[global]
Instance Pred_le_PreOrder {A B} : PreOrder (@Pred_le A B).
Proof.
  constructor.
  - intros R a b H. exact H.
  - intros R1 R2 R3 H12 H23 a b H. apply H23, H12, H.
Qed.

#[global]
Instance Arrow_Pred : Arrow Pred := {
  arr_pure := fun A B f a b => f a = b ;
  arr_comp := fun A B C f g a c => exists b, f a b /\ g b c ;
  arr_first := fun A B C f p q =>
    let '(a, c) := p in let '(b, c') := q in f a b /\ c = c'
}.

#[global]
Instance ArrowChoice_Pred : ArrowChoice Pred := {
  arr_left := fun A B C f x y =>
    match x, y with
    | inl a, inl b => f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end
}.

#[global]
Instance ArrowApply_Pred : ArrowApply Pred := {
  arr_app := fun A B p b =>
    let '(f, a) := p in f a b
}.

#[global]
Instance ArrowLoop_Pred : ArrowLoop Pred := {
  arr_loop := fun A B C f a b => exists c, f (a, c) (b, c)
}.

(* ================================================================= *)
(** ** [Pred A] is a monad in its second argument                     *)
(* ================================================================= *)

(** For every fixed source type [A], [fun B => Pred A B = A -> B -> Prop]
    is a monad in [B] via relational composition.  The source [A] is
    threaded as a shared "context" through [ret] and [bind]:

        ret b    := fun _ b' => b = b'
        bind m k := fun a  c => exists b, m a b /\ k b a c

    The monad laws hold under pointwise logical equivalence
    ([Eq1_Pred]), with no extensionality axioms required. *)

Section PredMonad.
  Context {A : Type}.

  Definition retPred {B} (b : B) : Pred A B :=
    fun _ b' => b = b'.

  Definition bindPred {B C}
    (m : Pred A B) (k : B -> Pred A C) : Pred A C :=
    fun a c => exists b, m a b /\ k b a c.

  #[global]
  Instance Monad_Pred : Monad (Pred A) := {
    ret := @retPred ;
    bind := @bindPred
  }.

  #[global]
  Instance Eq1_Pred : Eq1 (Pred A) :=
    fun B m1 m2 => forall a b, m1 a b <-> m2 a b.

End PredMonad.

(* ================================================================= *)
(** ** [optionPred] alias                                             *)
(* ================================================================= *)

(** The generic [optionArrT] transformer specializes cleanly to
    [Pred].  [ArrowChoice], [ArrowApply] and [ArrowLoop] instances are
    inherited from the generic [ArrowChoice_optionArrT] etc. in
    [Classes/OptionArrowT]; their laws likewise come through the
    generic [ArrowChoiceLaws_optionArrT] etc. applied to [Pred]'s own
    arrow laws. *)

Definition optionPred := optionArrT Pred.

(** Pointwise iff for [optionPred].  [optionPred A B = Pred A (option B)]
    so this is just [Pred_eq] at that type. *)
Definition optionPred_eq {A B} (f g : optionPred A B) : Prop :=
  forall a ob, f a ob <-> g a ob.

(* ================================================================= *)
(** ** Arrow-view specification types                                 *)
(* ================================================================= *)

Section ArrowSpec.

  Variable S : Type.

  (** For [prog] and [ndprog]: stateful computation with possible
      failure.  Unfolds to [(unit * S) -> option (A * S) -> Prop]. *)
  Definition progPredArr (A : Type) : Type :=
    stateArrT S (optionArrT Pred) unit A.

  (** For [nditprog]: stateful computation with failure and
      divergence.  Unfolds to [(unit * S) -> option (option (A * S)) -> Prop].
      The outer [option] represents exceptions; the inner [option]
      represents divergence. *)
  Definition nditPredArr (A : Type) : Type :=
    stateArrT S (optionArrT (optionArrT Pred)) unit A.

End ArrowSpec.

(* ================================================================= *)
(** ** Monad-view specification types                                 *)
(* ================================================================= *)

Section MonadSpec.

  Variable S : Type.

  (** For [prog]/[ndprog].  Chains: base [Pred unit] through [optionT]
      and [stateT], inheriting [Monad], [Eq1], and [MonadLawsE] from
      the transformer instances in [ProgFacts.v]. *)
  Definition progPredM (A : Type) : Type :=
    stateT S (optionT (Pred unit)) A.

  (** For [nditprog] (double [optionT] for exception + divergence). *)
  Definition nditPredM (A : Type) : Type :=
    stateT S (optionT (optionT (Pred unit))) A.

End MonadSpec.
