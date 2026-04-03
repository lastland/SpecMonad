(** * Monad law proofs for [nditprog].

    [nditprog S = stateT S (optionT (optionT SetM))] combines
    state, exceptions, nontermination, and nondeterminism.

    Since [SetM] satisfies [MonadLawsE] (from [NonDetProgFacts]),
    the generic [optionT] and [stateT] towers from [ProgFacts]
    lift the laws through two [optionT] layers and one [stateT]
    layer with zero additional proof work. *)

From Coq Require Import Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness Require Import
  Taxonomy.NonDetProg
  Taxonomy.NonDetItProg
  Taxonomy.ProgFacts
  Taxonomy.NonDetProgFacts.

Section NonDetItProgFacts.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_SetM]
      → [Eq1_optionT]  (inner: divergence layer)
      → [Eq1_optionT]  (outer: exception layer)
      → [Eq1_stateT]

      and similarly for [MonadLawsE]. *)

  Definition Eq1__nditprog : Eq1 (nditprog S) :=
    Eq1_stateT S (optionT (optionT SetM)).

  Definition MonadLawsE__nditprog
    : @MonadLawsE (nditprog S) _ (Monad__nditprog S) :=
    MonadLawsE_stateT S (optionT (optionT SetM)).

End NonDetItProgFacts.
