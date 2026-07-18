(** * The fixed-input predicate monad on [Rel].

    For every fixed source type [A], the second-argument projection
    [fun B => Rel A B = A -> B -> Prop] is a monad in [B] via relational
    composition.  The source [A] is threaded as a shared "context"
    through [ret] and [bind]:

        ret b    := fun _ b' => b = b'
        bind m k := fun a  c => exists b, m a b /\ k b a c

    The monad laws hold under pointwise logical equivalence
    ([Eq1_Rel]), with no extensionality axioms required.

    This file also exposes the monad-view specification types for the
    three computation monads ([prog], [ndprog], [nditprog]):

        [progPredM S A = stateT S (optionT (Rel unit)) A]
        [nditPredM S A = stateT S (optionT (optionT (Rel unit))) A]

    The monad view inherits [MonadLawsE] automatically via the generic
    [MonadLawsE_optionT] and [MonadLawsE_stateT] instances in
    [Taxonomy/ProgFacts.v].  Laws are proved in
    [Taxonomy/PredMonadFacts.v]. *)

From Coq Require Import
  Morphisms RelationClasses.
From ExtLib Require Import
  Monad
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy Require Import Rel.

(* ================================================================= *)
(** ** [Rel A] is a monad in its second argument                     *)
(* ================================================================= *)

Section PredMonad.
  Context {A : Type}.

  Definition retPred {B} (b : B) : Rel A B :=
    fun _ b' => b = b'.

  Definition bindPred {B C}
    (m : Rel A B) (k : B -> Rel A C) : Rel A C :=
    fun a c => exists b, m a b /\ k b a c.

  #[global]
  Instance Monad_Rel : Monad (Rel A) := {
    ret := @retPred ;
    bind := @bindPred
  }.

  #[global]
  Instance Eq1_Rel : Eq1 (Rel A) :=
    fun B m1 m2 => forall a b, m1 a b <-> m2 a b.

End PredMonad.

(* ================================================================= *)
(** ** Monad-view specification types                                 *)
(* ================================================================= *)

Section MonadSpec.

  Variable S : Type.

  (** For [prog]/[ndprog].  Chains: base [Rel unit] through [optionT]
      and [stateT], inheriting [Monad], [Eq1], and [MonadLawsE] from
      the transformer instances in [ProgFacts.v]. *)
  Definition progPredM (A : Type) : Type :=
    stateT S (optionT (Rel unit)) A.

  (** For [nditprog] (double [optionT] for exception + divergence). *)
  Definition nditPredM (A : Type) : Type :=
    stateT S (optionT (optionT (Rel unit))) A.

End MonadSpec.
