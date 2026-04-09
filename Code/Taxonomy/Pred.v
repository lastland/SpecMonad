(** * The relational predicate monad [Pred] and composed spec types.

    [Pred A B := A -> B -> Prop] is defined in [Code/Classes/Arrow.v]
    where its [Arrow] / [ArrowChoice] / [ArrowApply] / [ArrowLoop]
    instances and their laws are also proved.  This file adds the
    complementary monad view: for every fixed [A], the partially
    applied type [fun B => Pred A B] is a monad in [B] via relational
    composition.

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

    This file holds the definitions and [Monad] / [Eq1] /
    [ArrowChoice] / [ArrowApply] / [ArrowLoop] instances.  Their laws
    ([Eq1Equivalence], [MonadLawsE], [ArrowLaws]) are proved in
    [Taxonomy/PredFacts.v]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import
  Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy Require Import ProgFacts.

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
    generic [ArrowChoiceLaws_optionArrT] etc.  [PredFacts.v] provides
    direct relational characterizations of [arr_comp] and [arr_first]
    and reproves [ArrowLaws_optionPred] in that direct form. *)

Definition optionPred := optionArrT Pred.

Lemma optionPred_eq {A B} (f g : optionPred A B) :
  (forall a ob, f a ob <-> g a ob) -> f = g.
Proof.
  intros H. extensionality a. extensionality ob.
  apply propositional_extensionality. apply H.
Qed.

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
