From ExtLib Require Import OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws.

Import MonadNotation.
Open Scope monad_scope.

(** * Specification monads with divergence and exceptions, without state

    Two [optionT] layers extend the pure [DSPSP] and [ASLPSP] carriers
    with separate exception and divergence indices.  For a precondition
    [p : Prop], the runners expose a predicate on full outcomes.  The
    observation in [DivExcNonDet_SPDivExc.v] gives those indices these meanings:

    - [Some (Some a)] : successful return with value [a]
    - [Some None]     : exception
    - [None]          : divergence

    These are specification carriers, not sets of computation outcomes.
    Their monad laws and monotone binds lift from the pure bases through
    the generic results in [TransformerLaws.v]. *)

Section DivExcSP.

  Definition DSPDivExc : Type -> Type := optionT (optionT DSPSP).
  Definition ASLPDivExc : Type -> Type := optionT (optionT ASLPSP).

  Definition runDSPDivExc {A} (m : DSPDivExc A) : Prop -> option (option A) -> Prop :=
    getDSP (unOptionT (unOptionT m)).

  Definition runASLPDivExc {A} (m : ASLPDivExc A) : Prop -> option (option A) -> Prop :=
    getASLP (unOptionT (unOptionT m)).

  (** ** Monad laws up to pointwise logical equivalence *)

  #[global] Instance Monad__DSPDivExc : Monad DSPDivExc :=
    @Monad_optionT (optionT DSPSP) (@Monad_optionT DSPSP Monad_DSPSP).

  #[global] Instance Eq1__DSPDivExc : Eq1 DSPDivExc :=
    Eq1_optionT (optionT DSPSP).

  #[global] Instance Eq1Equivalence__DSPDivExc
    : @Eq1Equivalence DSPDivExc _ Eq1__DSPDivExc :=
    Eq1Equivalence_optionT (optionT DSPSP).

  #[global] Instance MonadLawsE__DSPDivExc
    : @MonadLawsE DSPDivExc Eq1__DSPDivExc Monad__DSPDivExc :=
    MonadLawsE_optionT (optionT DSPSP).

  #[global] Instance Monad__ASLPDivExc : Monad ASLPDivExc :=
    @Monad_optionT (optionT ASLPSP) (@Monad_optionT ASLPSP Monad_ASLPSP).

  #[global] Instance Eq1__ASLPDivExc : Eq1 ASLPDivExc :=
    Eq1_optionT (optionT ASLPSP).

  #[global] Instance Eq1Equivalence__ASLPDivExc
    : @Eq1Equivalence ASLPDivExc _ Eq1__ASLPDivExc :=
    Eq1Equivalence_optionT (optionT ASLPSP).

  #[global] Instance MonadLawsE__ASLPDivExc
    : @MonadLawsE ASLPDivExc Eq1__ASLPDivExc Monad__ASLPDivExc :=
    MonadLawsE_optionT (optionT ASLPSP).

  (** ** Refinement orders and monotonicity

      Both orders are forward implication at every precondition and full
      outcome, rather than comparison at one chosen precondition. *)

  Definition ordDSPDivExc {A} (m n : DSPDivExc A) : Prop :=
    ordDSPSP (unOptionT (unOptionT m)) (unOptionT (unOptionT n)).

  Definition ordASLPDivExc {A} (m n : ASLPDivExc A) : Prop :=
    ordASLPSP (unOptionT (unOptionT m)) (unOptionT (unOptionT n)).

  Lemma ordDSPDivExc_refl {A} (m : DSPDivExc A) : ordDSPDivExc m m.
  Proof. apply ordDSPSP_refl. Qed.

  Lemma ordASLPDivExc_refl {A} (m : ASLPDivExc A) : ordASLPDivExc m m.
  Proof. apply ordASLPSP_refl. Qed.

  (** The pure collapse makes ordered bind possible: [DSPSP] presents
      [ASPSP], and [ASLPSP] presents [DSLPSP].  Their binds pass the prefix's
      postcondition at each intermediate value to the corresponding
      continuation as its precondition.  Precondition monotonicity then
      combines with the pointwise order to give
      [bindDSP_mono] and [bindASLP_mono], without stateful relation recovery.

      Adding option layers changes the outcome indices, not the [Prop]
      precondition.  This does not contradict the Boolean-state no-go result in
      [SPBindOrderCounterexample.v]: that result concerns stateful carriers
      with preconditions [bool -> Prop] and their current return and order.

      At each option layer, bind uses the continuation only for [Some a];
      [None] propagates unchanged.  The generic [bind_optionT_mono] uses
      the continuation order in the first case and reflexivity in the
      second, so it lifts both base results through two layers. *)

  Lemma bindDSPDivExc_mono {A B} (m n : DSPDivExc A) (f g : A -> DSPDivExc B) :
    ordDSPDivExc m n -> (forall a, ordDSPDivExc (f a) (g a)) ->
    ordDSPDivExc (bind m f) (bind n g).
  Proof.
    exact (@bind_optionT_mono (optionT DSPSP) _ (@ord_optionT DSPSP (@ordDSPSP))
      (@ord_optionT_refl DSPSP (@ordDSPSP) ordDSPSP_refl)
      (@bind_optionT_mono DSPSP _ (@ordDSPSP) ordDSPSP_refl (@bindDSP_mono))
      A B m n f g).
  Qed.

  Lemma bindASLPDivExc_mono {A B} (m n : ASLPDivExc A) (f g : A -> ASLPDivExc B) :
    ordASLPDivExc m n -> (forall a, ordASLPDivExc (f a) (g a)) ->
    ordASLPDivExc (bind m f) (bind n g).
  Proof.
    exact (@bind_optionT_mono (optionT ASLPSP) _ (@ord_optionT ASLPSP (@ordASLPSP))
      (@ord_optionT_refl ASLPSP (@ordASLPSP) ordASLPSP_refl)
      (@bind_optionT_mono ASLPSP _ (@ordASLPSP) ordASLPSP_refl (@bindASLP_mono))
      A B m n f g).
  Qed.

End DivExcSP.
