(** * Monad morphisms at three levels, each a lift of a base one

    Computations are nondeterministic and may diverge.  The base computation
    monad is the non-empty fragment [divndNE], and the two others are monad
    transformers applied to it, so every computation has an outcome from
    every start state by construction:

      base        [divndNE]
      state       [stdivndNE S]     = [stateT S divndNE]
      state+exc   [stdivexcndNE S]  = [stateT S (optionT divndNE)]

    Each of the eight predicate-transformer readings is defined ONCE, at the
    base, and lifted:

      WP   a monad morphism [divndNE ~> WPure], lifted by the monad
           transformers ([MonadMorphism_stateT], [MonadMorphism_optionT]) to
           [stdivndNE S ~> WSt S] and [stdivexcndNE S ~> WStExc S];

      SP   a base arrow morphism [Rel ~> arr] ([Arrows/SPostArrEquiv.v]),
           lifted by the arrow transformers ([state_arrow_morphism],
           [state_option_arrow_morphism]) and applied to the relation
           between start states and terminating outcomes.  An arrow morphism
           is a monad morphism at each fixed input ([arrow_morphism_monad]),
           so these are monad morphisms into [ASP], [ASPSt S], [ASPStExc S]
           and their DSLP, DSP, ASLP counterparts.

    All twenty-four have an [IsMonadMorphism] instance, so each has its
    [triple] ([Triple.v]).  The triples lift with them:

      WP   the triple at a stack is the base triple, start state by start
           state ([triple_dwpSt] &c.);

      SP   the triples at the three levels are the judgement on one base
           arrow at three pairs of indices ([triple_aspPure],
           [triple_aspSt], [triple_aspStExc] &c.).  The arrow
           transformers change only the indices.

    An SP triple does not in general split start state by start state: an
    incorrectness triple at the state level asks for SOME start state per
    outcome.  And at the input [unit] of the base monads DSP coincides with
    ASP and ASLP with DSLP ([DSPMonad.v], [ASLPMonad.v]); what tells the
    four apart is the base arrow at an arbitrary input. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import
  Arrow OptionArrowT StateArrowT ArrowMonad ArrowMorphism RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Computation Require Import
  DivNonDetNE.
From Incorrectness.Relational Require Import
  Rel RelSPostArr.
From Incorrectness.Taxonomy.Arrows Require Import
  SPostArr SPostArrEquiv.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  WPureMonad ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Relational Require PredMonad RelMonads.
From Incorrectness.Taxonomy.Triples Require Import Triple.

Local Notation Pred := PredMonad.PredM.Pred.
Local Notation Monad_Pred := PredMonad.PredM.Monad_Pred.
Local Notation Eq1_Pred := PredMonad.PredM.Eq1_Pred.
Local Notation Eq1Equivalence_Pred := PredMonad.PredMFacts.Eq1Equivalence_Pred.
Local Notation MonadLawsE_Pred := PredMonad.PredMFacts.MonadLawsE_Pred.

(* ================================================================= *)
(** * WP: four base monad morphisms, lifted by the monad transformers *)
(* ================================================================= *)

(** A demonic reading asks every outcome to be good, an angelic one asks
    some outcome to be.  A total reading counts divergence as bad, a liberal
    one as good. *)

Section BaseWP.

  Definition demonic (div : Prop) {A} (d : divndNE A) (post : A -> Prop) : Prop :=
    forall oa, unOptionT (getNE d) oa ->
      match oa with Some a => post a | None => div end.

  Definition angelic (div : Prop) {A} (d : divndNE A) (post : A -> Prop) : Prop :=
    exists oa, unOptionT (getNE d) oa /\
      match oa with Some a => post a | None => div end.

  Lemma demonic_mono (div : Prop) {A} (d : divndNE A) : wpure_mono (demonic div d).
  Proof.
    intros p q Hpq H oa Ho. specialize (H oa Ho).
    destruct oa as [a|]; [ exact (Hpq a H) | exact H ].
  Qed.

  Lemma angelic_mono (div : Prop) {A} (d : divndNE A) : wpure_mono (angelic div d).
  Proof.
    intros p q Hpq [oa [Ho H]]. exists oa. split; [ exact Ho |].
    destruct oa as [a|]; [ exact (Hpq a H) | exact H ].
  Qed.

  Definition demonicWP (div : Prop) : forall A, divndNE A -> WPure A :=
    fun A d => mkWPure (demonic div d) (demonic_mono div d).

  Definition angelicWP (div : Prop) : forall A, divndNE A -> WPure A :=
    fun A d => mkWPure (angelic div d) (angelic_mono div d).

  Theorem demonicWP_morphism (div : Prop) :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure (demonicWP div).
  Proof.
    constructor.
    - intros A x y Hxy p. split; intros H oa Ho.
      + exact (H oa (proj2 (eq1_outcomes x y Hxy oa) Ho)).
      + exact (H oa (proj1 (eq1_outcomes x y Hxy oa) Ho)).
    - intros A a p. split.
      + intro H. exact (H (Some a) eq_refl).
      + intros H oa Ho. cbn in Ho. subst oa. exact H.
    - intros A B x k p. split.
      + intros H oa Ho. destruct oa as [a|].
        * intros ob Hob. apply H.
          apply (proj2 (DivNonDetNE.outcomes_bind (getNE x) (fun a => getNE (k a)) ob)).
          exists (Some a). exact (conj Ho Hob).
        * refine (H None _).
          apply (proj2 (DivNonDetNE.outcomes_bind (getNE x) (fun a => getNE (k a)) None)).
          exists None. exact (conj Ho eq_refl).
      + intros H ob Hob.
        apply (proj1 (DivNonDetNE.outcomes_bind (getNE x)
                        (fun a => getNE (k a)) ob)) in Hob.
        destruct Hob as [[a|] [Ho Hk]].
        * exact (H (Some a) Ho ob Hk).
        * subst ob. exact (H None Ho).
  Qed.

  Theorem angelicWP_morphism (div : Prop) :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure (angelicWP div).
  Proof.
    constructor.
    - intros A x y Hxy p. split; intros [oa [Ho H]]; exists oa; split; try exact H.
      + exact (proj1 (eq1_outcomes x y Hxy oa) Ho).
      + exact (proj2 (eq1_outcomes x y Hxy oa) Ho).
    - intros A a p. split.
      + intros [oa [Ho H]]. cbn in Ho. subst oa. exact H.
      + intro H. exists (Some a). exact (conj eq_refl H).
    - intros A B x k p. split.
      + intros [ob [Hob H]].
        apply (proj1 (DivNonDetNE.outcomes_bind (getNE x)
                        (fun a => getNE (k a)) ob)) in Hob.
        destruct Hob as [[a|] [Ho Hk]].
        * exists (Some a). split; [ exact Ho |]. exists ob. exact (conj Hk H).
        * subst ob. exists None. exact (conj Ho H).
      + intros [[a|] [Ho H]].
        * destruct H as [ob [Hob H]]. exists ob. split; [| exact H ].
          apply (proj2 (DivNonDetNE.outcomes_bind (getNE x) (fun a => getNE (k a)) ob)).
          exists (Some a). exact (conj Ho Hob).
        * exists None. split; [| exact H ].
          apply (proj2 (DivNonDetNE.outcomes_bind (getNE x) (fun a => getNE (k a)) None)).
          exists None. exact (conj Ho eq_refl).
  Qed.
End BaseWP.

(** The four readings. *)
Definition dwpPure  {A} (d : divndNE A) : WPure A := demonicWP False A d.
Definition dwlpPure {A} (d : divndNE A) : WPure A := demonicWP True A d.
Definition awpPure  {A} (d : divndNE A) : WPure A := angelicWP False A d.
Definition awlpPure {A} (d : divndNE A) : WPure A := angelicWP True A d.

(** A base morphism into [WPure], under [stateT], and under [stateT] over
    [optionT]. *)
Section LiftedWP.
  Variable σ : forall A, divndNE A -> WPure A.
  Hypothesis Hσ :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure σ.
  Variable S : Type.

  Theorem wpSt_morphism :
    @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
      (Eq1__stdivndNE S) (Eq1__WSt S) (stateT_map S σ).
  Proof.
    exact (@MonadMorphism_stateT divndNE WPure Monad__divndNE Monad_WPure
             Eq1__divndNE Eq1_WPure Eq1Equivalence_WPure MonadLawsE_WPure
             S σ Hσ).
  Qed.

  Theorem wpStExc_morphism :
    @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
      (Eq1__stdivexcndNE S) (Eq1__WStExc S) (stateT_map S (optionT_map σ)).
  Proof.
    exact (@MonadMorphism_stateT (optionT divndNE) (optionT WPure)
             (@Monad_optionT divndNE Monad__divndNE)
             (@Monad_optionT WPure Monad_WPure)
             (@Eq1_optionT divndNE Eq1__divndNE) (@Eq1_optionT WPure Eq1_WPure)
             (@Eq1Equivalence_optionT WPure Monad_WPure Eq1_WPure
                Eq1Equivalence_WPure)
             (@MonadLawsE_optionT WPure Monad_WPure Eq1_WPure
                Eq1Equivalence_WPure MonadLawsE_WPure)
             S (optionT_map σ)
             (@MonadMorphism_optionT divndNE WPure Monad__divndNE Monad_WPure
                Eq1__divndNE Eq1_WPure Eq1Equivalence_WPure MonadLawsE_WPure
                σ Hσ)).
  Qed.

  (** The triple at a stack is the base triple, start state by start state.
      At state+exceptions the base triple is at the result type
      [option (A * S)]. *)
  Lemma spec_holds_wpSt {A} (m : stdivndNE S A) (k : approxKind)
    (P : S -> Prop) (Q : A * S -> Prop) :
    spec_holds (stateT_map S σ A m : WSt S A) k P Q
    <-> forall s, spec_holds (σ _ (runStateT m s)) k (fun _ => P s) Q.
  Proof.
    exact (pt_holds_pointwise
             (fun Q' s => getWPure (σ _ (runStateT m s)) Q') k P Q).
  Qed.

  Lemma spec_holds_wpStExc {A} (m : stdivexcndNE S A) (k : approxKind)
    (P : S -> Prop) (Q : option (A * S) -> Prop) :
    spec_holds (stateT_map S (optionT_map σ) A m : WStExc S A) k P Q
    <-> forall s,
          spec_holds (σ _ (unOptionT (runStateT m s))) k (fun _ => P s) Q.
  Proof.
    exact (pt_holds_pointwise
             (fun Q' s => getWPure (σ _ (unOptionT (runStateT m s))) Q') k P Q).
  Qed.
End LiftedWP.

(** The four readings at the three levels, each a monad morphism. *)

Lemma dwpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@dwpPure).
Proof. exact (demonicWP_morphism False). Qed.

Definition dwpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@dwpPure) A m.
Definition dwpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@dwpPure)) A m.

Lemma dwpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@dwpSt S).
Proof. exact (wpSt_morphism (@dwpPure) dwpPure_morphism S). Qed.

Lemma dwpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@dwpStExc S).
Proof. exact (wpStExc_morphism (@dwpPure) dwpPure_morphism S). Qed.

#[global] Instance IsMonadMorphism_dwpPure : IsMonadMorphism (@dwpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dwpPure_morphism.
#[global] Instance IsMonadMorphism_dwpSt (S : Type) :
  IsMonadMorphism (@dwpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwpSt_morphism S).
#[global] Instance IsMonadMorphism_dwpStExc (S : Type)
  : IsMonadMorphism (@dwpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwpStExc_morphism S).

Theorem triple_dwpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dwpSt S) m k P Q
  <-> forall s, triple (@dwpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@dwpPure) S m k P Q). Qed.

Theorem triple_dwpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dwpStExc S) m k P Q
  <-> forall s,
        triple (@dwpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@dwpPure) S m k P Q). Qed.

Lemma dwlpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@dwlpPure).
Proof. exact (demonicWP_morphism True). Qed.

Definition dwlpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@dwlpPure) A m.
Definition dwlpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@dwlpPure)) A m.

Lemma dwlpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@dwlpSt S).
Proof. exact (wpSt_morphism (@dwlpPure) dwlpPure_morphism S). Qed.

Lemma dwlpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@dwlpStExc S).
Proof. exact (wpStExc_morphism (@dwlpPure) dwlpPure_morphism S). Qed.

#[global] Instance IsMonadMorphism_dwlpPure : IsMonadMorphism (@dwlpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dwlpPure_morphism.
#[global] Instance IsMonadMorphism_dwlpSt (S : Type) :
  IsMonadMorphism (@dwlpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwlpSt_morphism S).
#[global] Instance IsMonadMorphism_dwlpStExc (S : Type)
  : IsMonadMorphism (@dwlpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwlpStExc_morphism S).

Theorem triple_dwlpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dwlpSt S) m k P Q
  <-> forall s, triple (@dwlpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@dwlpPure) S m k P Q). Qed.

Theorem triple_dwlpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dwlpStExc S) m k P Q
  <-> forall s,
        triple (@dwlpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@dwlpPure) S m k P Q). Qed.

Lemma awpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@awpPure).
Proof. exact (angelicWP_morphism False). Qed.

Definition awpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@awpPure) A m.
Definition awpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@awpPure)) A m.

Lemma awpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@awpSt S).
Proof. exact (wpSt_morphism (@awpPure) awpPure_morphism S). Qed.

Lemma awpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@awpStExc S).
Proof. exact (wpStExc_morphism (@awpPure) awpPure_morphism S). Qed.

#[global] Instance IsMonadMorphism_awpPure : IsMonadMorphism (@awpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ awpPure_morphism.
#[global] Instance IsMonadMorphism_awpSt (S : Type) :
  IsMonadMorphism (@awpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awpSt_morphism S).
#[global] Instance IsMonadMorphism_awpStExc (S : Type)
  : IsMonadMorphism (@awpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awpStExc_morphism S).

Theorem triple_awpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@awpSt S) m k P Q
  <-> forall s, triple (@awpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@awpPure) S m k P Q). Qed.

Theorem triple_awpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@awpStExc S) m k P Q
  <-> forall s,
        triple (@awpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@awpPure) S m k P Q). Qed.

Lemma awlpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@awlpPure).
Proof. exact (angelicWP_morphism True). Qed.

Definition awlpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@awlpPure) A m.
Definition awlpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@awlpPure)) A m.

Lemma awlpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@awlpSt S).
Proof. exact (wpSt_morphism (@awlpPure) awlpPure_morphism S). Qed.

Lemma awlpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@awlpStExc S).
Proof. exact (wpStExc_morphism (@awlpPure) awlpPure_morphism S). Qed.

#[global] Instance IsMonadMorphism_awlpPure : IsMonadMorphism (@awlpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ awlpPure_morphism.
#[global] Instance IsMonadMorphism_awlpSt (S : Type) :
  IsMonadMorphism (@awlpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awlpSt_morphism S).
#[global] Instance IsMonadMorphism_awlpStExc (S : Type)
  : IsMonadMorphism (@awlpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awlpStExc_morphism S).

Theorem triple_awlpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@awlpSt S) m k P Q
  <-> forall s, triple (@awlpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@awlpPure) S m k P Q). Qed.

Theorem triple_awlpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@awlpStExc S) m k P Q
  <-> forall s,
        triple (@awlpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@awlpPure) S m k P Q). Qed.

(* ================================================================= *)
(** * SP: four base arrow morphisms, lifted by the arrow transformers *)
(* ================================================================= *)

(** ** The terminating outcomes of a computation *)

(** At the base they are a set of results.  Divergence is dropped; this is a
    monad morphism into [Pred], and the monad transformers lift it. *)
Definition sliceNE {A} (d : divndNE A) : Pred A :=
  fun a => unOptionT (getNE d) (Some a).

Theorem sliceNE_morphism :
  @MonadMorphism divndNE Pred Monad__divndNE Monad_Pred
    Eq1__divndNE Eq1_Pred (@sliceNE).
Proof.
  constructor.
  - intros A x y Hxy a. exact (eq1_outcomes x y Hxy (Some a)).
  - intros A a a'. change (Some a' = Some a <-> a' = a). split.
    + intro H. inversion H. reflexivity.
    + intro H. subst a'. reflexivity.
  - intros A B x k b.
    change (unOptionT (bindD (getNE x) (fun a => getNE (k a))) (Some b)
            <-> exists a, unOptionT (getNE x) (Some a)
                          /\ unOptionT (getNE (k a)) (Some b)).
    etransitivity;
      [ exact (DivNonDetNE.outcomes_bind (getNE x) (fun a => getNE (k a)) (Some b)) |].
    split.
    + intros [[a|] [Ho Hk]]; [ exists a; exact (conj Ho Hk) | discriminate Hk ].
    + intros [a [Ho Hk]]. exists (Some a). exact (conj Ho Hk).
Qed.

(** ** A stack of [Pred] as a stack of the relation arrow

    An element of a [Pred] stack is, at the input [unit], an element of the
    corresponding stack of [Rel]: the relation between a start state and an
    outcome.  [ret] and [bind] agree. *)

Definition RelArrow_Rel : @RelArrow Rel Arrow_Rel :=
  {| rel_reading := fun A B (f : Rel A B) => f ;
     rel_pure := fun A B f a b => iff_refl _ ;
     rel_comp := fun A B C f g a c => iff_refl _ ;
     rel_first := fun A B C f a c b d => iff_refl _ |}.

Lemma RelArrowChoice_Rel
  : @RelArrowChoice Rel Arrow_Rel ArrowChoice_Rel RelArrow_Rel.
Proof. constructor. intros A B C f [a|c] [b|d]; reflexivity. Qed.

Lemma RelArrowApply_Rel
  : @RelArrowApply Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel.
Proof. constructor. intros A B f a b. reflexivity. Qed.

Definition outcomes0 {A} (p : Pred A) : Rel unit A :=
  fun _ a => p a.
Definition outcomesSt {S A} (m : stateT S Pred A) : stateArrT S Rel unit A :=
  fun us r => runStateT m (snd us) r.
Definition outcomesStExc {S A} (m : stateT S (optionT Pred) A)
  : stateArrT S (optionArrT Rel) unit A :=
  fun us o => unOptionT (runStateT m (snd us)) o.

Theorem outcomes0_morphism :
  @MonadMorphism Pred (Rel unit) Monad_Pred
    (@Monad_Arrow Rel Arrow_Rel ArrowApply_Rel unit)
    Eq1_Pred (@Eq1_Arrow Rel ArrowEq_Rel unit) (@outcomes0).
Proof.
  constructor.
  - intros A p q H u a. exact (H a).
  - intros A a u b. change (b = a <-> a = b). split; intro H; exact (eq_sym H).
  - intros A B p k u b. symmetry.
    exact (@rel_bind Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel RelArrowApply_Rel
             unit A B (outcomes0 p) (fun a => outcomes0 (k a)) u b).
Qed.

Theorem outcomesSt_morphism (S : Type) :
  @MonadMorphism (stateT S Pred) (stateArrT S Rel unit)
    (@Monad_stateT S Pred Monad_Pred)
    (@Monad_Arrow (stateArrT S Rel) (@Arrow_stateArrT S Rel Arrow_Rel)
       (@ArrowApply_stateArrT S Rel Arrow_Rel ArrowApply_Rel) unit)
    (@Eq1_stateT S Pred Eq1_Pred)
    (@Eq1_Arrow (stateArrT S Rel) (@ArrowEq_stateArrT S Rel ArrowEq_Rel) unit)
    (fun A => @outcomesSt S A).
Proof.
  constructor.
  - intros A x y H [u s] r. exact (H s r).
  - intros A a [u s] r. change (r = (a, s) <-> (a, s) = r).
    split; intro H; exact (eq_sym H).
  - intros A B x k [u s] r.
    etransitivity;
      [| symmetry;
         exact (@relS_bind Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel
                  RelArrowApply_Rel S unit A B (outcomesSt x)
                  (fun a => outcomesSt (k a)) u s r) ].
    split.
    + intros [[a s'] [H1 H2]]. exists a, s'. exact (conj H1 H2).
    + intros [a [s' [H1 H2]]]. exists (a, s'). exact (conj H1 H2).
Qed.

Theorem outcomesStExc_morphism (S : Type) :
  @MonadMorphism (stateT S (optionT Pred)) (stateArrT S (optionArrT Rel) unit)
    (@Monad_stateT S (optionT Pred) (@Monad_optionT Pred Monad_Pred))
    (@Monad_Arrow (stateArrT S (optionArrT Rel))
       (@Arrow_stateArrT S (optionArrT Rel)
          (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel))
       (@ArrowApply_stateArrT S (optionArrT Rel)
          (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
          (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel))
       unit)
    (@Eq1_stateT S (optionT Pred) (@Eq1_optionT Pred Eq1_Pred))
    (@Eq1_Arrow (stateArrT S (optionArrT Rel))
       (@ArrowEq_stateArrT S (optionArrT Rel) (@ArrowEq_optionArrT Rel ArrowEq_Rel))
       unit)
    (fun A => @outcomesStExc S A).
Proof.
  constructor.
  - intros A x y H [u s] o. exact (H s o).
  - intros A a [u s] o. symmetry.
    exact (@relE_pure Rel Arrow_Rel RelArrow_Rel ArrowChoice_Rel S unit A
             (fun _ => a) u s o).
  - intros A B x k [u s] o.
    etransitivity;
      [| symmetry;
         exact (@relE_bind Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel
                  RelArrowApply_Rel ArrowChoice_Rel RelArrowChoice_Rel
                  S unit A B (outcomesStExc x)
                  (fun a => outcomesStExc (k a)) u s o) ].
    split; intros [o1 [H1 H2]]; exists o1; (split; [ exact H1 |]);
      destruct o1 as [[a s']|]; exact H2.
Qed.

(** ** The terminating outcomes, as an element of the relation stack *)

Local Notation OR := (optionArrT Rel).
Local Notation Arrow_OR := (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel).
Local Notation Apply_OR :=
  (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel).
Local Notation Eq_OR := (@ArrowEq_optionArrT Rel ArrowEq_Rel).

Local Notation Monad_Rel0 := (@Monad_Arrow Rel Arrow_Rel ArrowApply_Rel unit).
Local Notation Eq1_Rel0 := (@Eq1_Arrow Rel ArrowEq_Rel unit).
Local Notation Monad_RelSt S :=
  (@Monad_Arrow (stateArrT S Rel) (@Arrow_stateArrT S Rel Arrow_Rel)
     (@ArrowApply_stateArrT S Rel Arrow_Rel ArrowApply_Rel) unit).
Local Notation Eq1_RelSt S :=
  (@Eq1_Arrow (stateArrT S Rel) (@ArrowEq_stateArrT S Rel ArrowEq_Rel) unit).
Local Notation Monad_RelStExc S :=
  (@Monad_Arrow (stateArrT S OR) (@Arrow_stateArrT S OR Arrow_OR)
     (@ArrowApply_stateArrT S OR Arrow_OR Apply_OR) unit).
Local Notation Eq1_RelStExc S :=
  (@Eq1_Arrow (stateArrT S OR) (@ArrowEq_stateArrT S OR Eq_OR) unit).

Definition termRel {A} (d : divndNE A) : Rel unit A :=
  outcomes0 (sliceNE d).
Definition termRelSt {S A} (m : stdivndNE S A) : stateArrT S Rel unit A :=
  outcomesSt (stateT_map S (@sliceNE) A m).
Definition termRelStExc {S A} (m : stdivexcndNE S A) : stateArrT S OR unit A :=
  outcomesStExc (stateT_map S (optionT_map (@sliceNE)) A m).

Theorem termRel_morphism :
  @MonadMorphism divndNE (Rel unit) Monad__divndNE Monad_Rel0
    Eq1__divndNE Eq1_Rel0 (@termRel).
Proof.
  exact (@MonadMorphism_comp divndNE Pred (Rel unit)
           Monad__divndNE Monad_Pred Monad_Rel0
           Eq1__divndNE Eq1_Pred Eq1_Rel0
           (@Eq1Equivalence_Arrow Rel Arrow_Rel ArrowApply_Rel ArrowEq_Rel unit)
           (@sliceNE) (@outcomes0) sliceNE_morphism outcomes0_morphism).
Qed.

Theorem termRelSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (stateArrT S Rel unit) (Monad__stdivndNE S) (Monad_RelSt S)
    (Eq1__stdivndNE S) (Eq1_RelSt S) (@termRelSt S).
Proof.
  exact (@MonadMorphism_comp (stdivndNE S) (stateT S Pred) (stateArrT S Rel unit)
           (Monad__stdivndNE S) (@Monad_stateT S Pred Monad_Pred) (Monad_RelSt S)
           (Eq1__stdivndNE S) (@Eq1_stateT S Pred Eq1_Pred) (Eq1_RelSt S)
           (@Eq1Equivalence_Arrow (stateArrT S Rel)
              (@Arrow_stateArrT S Rel Arrow_Rel)
              (@ArrowApply_stateArrT S Rel Arrow_Rel ArrowApply_Rel)
              (@ArrowEq_stateArrT S Rel ArrowEq_Rel) unit)
           (stateT_map S (@sliceNE)) (fun A => @outcomesSt S A)
           (@MonadMorphism_stateT divndNE Pred Monad__divndNE Monad_Pred
              Eq1__divndNE Eq1_Pred Eq1Equivalence_Pred MonadLawsE_Pred
              S (@sliceNE) sliceNE_morphism)
           (outcomesSt_morphism S)).
Qed.

Theorem termRelStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (stateArrT S OR unit) (Monad__stdivexcndNE S)
    (Monad_RelStExc S) (Eq1__stdivexcndNE S) (Eq1_RelStExc S) (@termRelStExc S).
Proof.
  exact (@MonadMorphism_comp (stdivexcndNE S) (stateT S (optionT Pred))
           (stateArrT S OR unit)
           (Monad__stdivexcndNE S)
           (@Monad_stateT S (optionT Pred) (@Monad_optionT Pred Monad_Pred))
           (Monad_RelStExc S)
           (Eq1__stdivexcndNE S)
           (@Eq1_stateT S (optionT Pred) (@Eq1_optionT Pred Eq1_Pred))
           (Eq1_RelStExc S)
           (@Eq1Equivalence_Arrow (stateArrT S OR)
              (@Arrow_stateArrT S OR Arrow_OR)
              (@ArrowApply_stateArrT S OR Arrow_OR Apply_OR)
              (@ArrowEq_stateArrT S OR Eq_OR) unit)
           (stateT_map S (optionT_map (@sliceNE)))
           (fun A => @outcomesStExc S A)
           (@MonadMorphism_stateT (optionT divndNE) (optionT Pred)
              (@Monad_optionT divndNE Monad__divndNE)
              (@Monad_optionT Pred Monad_Pred)
              (@Eq1_optionT divndNE Eq1__divndNE) (@Eq1_optionT Pred Eq1_Pred)
              (@Eq1Equivalence_optionT Pred Monad_Pred Eq1_Pred
                 Eq1Equivalence_Pred)
              (@MonadLawsE_optionT Pred Monad_Pred Eq1_Pred
                 Eq1Equivalence_Pred MonadLawsE_Pred)
              S (optionT_map (@sliceNE))
              (@MonadMorphism_optionT divndNE Pred Monad__divndNE Monad_Pred
                 Eq1__divndNE Eq1_Pred Eq1Equivalence_Pred MonadLawsE_Pred
                 (@sliceNE) sliceNE_morphism))
           (outcomesStExc_morphism S)).
Qed.

(** ** The monad morphism a base arrow morphism gives, at the three levels *)

Section SPMorphisms.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HAA : @ArrowApply arr HA}
    {HE : ArrowEq arr}.
  Variable F : forall A B, Rel A B -> arr A B.

  Local Notation OA := (optionArrT arr).
  Local Notation Arrow_OA := (@Arrow_optionArrT arr HA HC).
  Local Notation Apply_OA := (@ArrowApply_optionArrT arr HA HC HAA).
  Local Notation Eq_OA := (@ArrowEq_optionArrT arr HE).

  Local Notation Monad_arr0 := (@Monad_Arrow arr HA HAA unit).
  Local Notation Eq1_arr0 := (@Eq1_Arrow arr HE unit).
  Local Notation Monad_arrSt S :=
    (@Monad_Arrow (stateArrT S arr) (@Arrow_stateArrT S arr HA)
       (@ArrowApply_stateArrT S arr HA HAA) unit).
  Local Notation Eq1_arrSt S :=
    (@Eq1_Arrow (stateArrT S arr) (@ArrowEq_stateArrT S arr HE) unit).
  Local Notation Monad_arrStExc S :=
    (@Monad_Arrow (stateArrT S OA) (@Arrow_stateArrT S OA Arrow_OA)
       (@ArrowApply_stateArrT S OA Arrow_OA Apply_OA) unit).
  Local Notation Eq1_arrStExc S :=
    (@Eq1_Arrow (stateArrT S OA) (@ArrowEq_stateArrT S OA Eq_OA) unit).

  Definition spPure {A} (d : divndNE A) : arr unit A :=
    F unit A (termRel d).

  Definition spSt {S A} (m : stdivndNE S A) : stateArrT S arr unit A :=
    state_arrow_map S F unit A (termRelSt m).

  Definition spStExc {S A} (m : stdivexcndNE S A) : stateArrT S OA unit A :=
    state_arrow_map S (option_arrow_map F) unit A (termRelStExc m).

  (** All three are [F] at one relation each: the arrow transformers change
      the indices and nothing else. *)
  Lemma spPure_unfold {A} (d : divndNE A) :
    spPure d = F unit A (fun _ a => unOptionT (getNE d) (Some a)).
  Proof. reflexivity. Qed.

  Lemma spSt_unfold {S A} (m : stdivndNE S A) :
    spSt m
    = F (unit * S)%type (A * S)%type (fun us r => outSt m (snd us) (Some r)).
  Proof. reflexivity. Qed.

  Lemma spStExc_unfold {S A} (m : stdivexcndNE S A) :
    spStExc m
    = F (unit * S)%type (option (A * S))
        (fun us o => outStExc m (snd us) (Some o)).
  Proof. reflexivity. Qed.

  (** *** Through the arrow-morphism lifting

      [F] is a morphism of arrows; the arrow transformers lift it
      ([state_arrow_morphism], [state_option_arrow_morphism]); an arrow
      morphism is a monad morphism at the input [unit]
      ([arrow_morphism_monad]). *)
  Section ByLifting.
    Hypothesis HF :
      ArrowMorphism Arrow_Rel ArrowChoice_Rel ArrowApply_Rel ArrowEq_Rel
        HA HC HAA HE F.
    Hypothesis HL : @ArrowLaws arr HA HE.
    Hypothesis HCL : @ArrowChoiceLaws arr HA HC HE.
    Hypothesis HXL : @ArrowApplyLaws arr HA HAA HE.

    Theorem spPure_morphism :
      @MonadMorphism divndNE (arr unit) Monad__divndNE Monad_arr0
        Eq1__divndNE Eq1_arr0 (fun A => @spPure A).
    Proof.
      exact (@MonadMorphism_comp divndNE (Rel unit) (arr unit)
               Monad__divndNE Monad_Rel0 Monad_arr0
               Eq1__divndNE Eq1_Rel0 Eq1_arr0
               (@Eq1Equivalence_Arrow arr HA HAA HE unit)
               (@termRel) (fun A => F unit A) termRel_morphism
               (arrow_morphism_monad F HF HL unit HXL)).
    Qed.

    Theorem spSt_morphism (S : Type) :
      @MonadMorphism (stdivndNE S) (stateArrT S arr unit) (Monad__stdivndNE S)
        (Monad_arrSt S) (Eq1__stdivndNE S) (Eq1_arrSt S) (fun A => @spSt S A).
    Proof.
      exact (@MonadMorphism_comp (stdivndNE S) (stateArrT S Rel unit)
               (stateArrT S arr unit)
               (Monad__stdivndNE S) (Monad_RelSt S) (Monad_arrSt S)
               (Eq1__stdivndNE S) (Eq1_RelSt S) (Eq1_arrSt S)
               (@Eq1Equivalence_Arrow (stateArrT S arr)
                  (@Arrow_stateArrT S arr HA)
                  (@ArrowApply_stateArrT S arr HA HAA)
                  (@ArrowEq_stateArrT S arr HE) unit)
               (@termRelSt S) (fun A => state_arrow_map S F unit A)
               (termRelSt_morphism S)
               (arrow_morphism_monad (state_arrow_map S F)
                  (state_arrow_morphism F HF HL S HXL)
                  (@ArrowLaws_stateArrT S arr HA HE HL) unit
                  (@ArrowApplyLaws_stateArrT S arr HA HAA HE HL HXL))).
    Qed.

    Theorem spStExc_morphism (S : Type) :
      @MonadMorphism (stdivexcndNE S) (stateArrT S OA unit) (Monad__stdivexcndNE S)
        (Monad_arrStExc S) (Eq1__stdivexcndNE S) (Eq1_arrStExc S)
        (fun A => @spStExc S A).
    Proof.
      exact (@MonadMorphism_comp (stdivexcndNE S) (stateArrT S OR unit)
               (stateArrT S OA unit)
               (Monad__stdivexcndNE S) (Monad_RelStExc S) (Monad_arrStExc S)
               (Eq1__stdivexcndNE S) (Eq1_RelStExc S) (Eq1_arrStExc S)
               (@Eq1Equivalence_Arrow (stateArrT S OA)
                  (@Arrow_stateArrT S OA Arrow_OA)
                  (@ArrowApply_stateArrT S OA Arrow_OA Apply_OA)
                  (@ArrowEq_stateArrT S OA Eq_OA) unit)
               (@termRelStExc S)
               (fun A => state_arrow_map S (option_arrow_map F) unit A)
               (termRelStExc_morphism S)
               (arrow_morphism_monad (state_arrow_map S (option_arrow_map F))
                  (state_option_arrow_morphism F HF HL S HCL HXL)
                  (@ArrowLaws_stateArrT S OA Arrow_OA Eq_OA
                     (@ArrowLaws_optionArrT arr HA HC HE HL HCL))
                  unit
                  (@ArrowApplyLaws_stateArrT S OA Arrow_OA Apply_OA Eq_OA
                     (@ArrowLaws_optionArrT arr HA HC HE HL HCL)
                     (@ArrowApplyLaws_optionArrT arr HA HC HAA HE HL HCL HXL)))).
    Qed.
  End ByLifting.

  (** *** Through the relations denoted

      When the arrow has relational semantics, its equality is equality of
      the relations denoted, and [rel_reading] inverts [F], the same three
      statements follow from [rel_pure], [rel_bind], [relS_bind],
      [relE_pure] and [relE_bind] alone.  The arrow laws of the two stacks
      are not used. *)
  Section ByRelations.
    Context {HR : @RelArrow arr HA} {HRC : @RelArrowChoice arr HA HC HR}
      {HRA : @RelArrowApply arr HA HAA HR} {HRE : @RelArrowEq arr HA HE HR}.
    Hypothesis HF : forall A B (R : Rel A B) a b,
        @rel_reading arr HA HR A B (F A B R) a b <-> R a b.

    Lemma ofRel_morphism :
      @MonadMorphism (Rel unit) (arr unit) Monad_Rel0 Monad_arr0
        Eq1_Rel0 Eq1_arr0 (fun A => F unit A).
    Proof.
      constructor.
      - intros A x y H.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE unit A
                        (F unit A x) (F unit A y))).
        intros u a.
        etransitivity; [ exact (HF unit A x u a) |].
        etransitivity; [ exact (H u a) |].
        symmetry. exact (HF unit A y u a).
      - intros A a.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE unit A _ _)).
        intros u b.
        etransitivity; [ exact (HF unit A _ u b) |].
        symmetry. exact (@rel_pure arr HA HR unit A (fun _ => a) u b).
      - intros A B m k.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE unit B _ _)).
        intros u b.
        etransitivity; [ exact (HF unit B _ u b) |].
        etransitivity;
          [ exact (@rel_bind Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel
                     RelArrowApply_Rel unit A B m k u b) |].
        etransitivity;
          [| symmetry;
             exact (@rel_bind arr HA HAA HR HRA unit A B (F unit A m)
                      (fun a => F unit B (k a)) u b) ].
        split; intros [a [H1 H2]]; exists a; split.
        + exact (proj2 (HF unit A m u a) H1).
        + exact (proj2 (HF unit B (k a) u b) H2).
        + exact (proj1 (HF unit A m u a) H1).
        + exact (proj1 (HF unit B (k a) u b) H2).
    Qed.

    Lemma ofRelSt_morphism (S : Type) :
      @MonadMorphism (stateArrT S Rel unit) (stateArrT S arr unit)
        (Monad_RelSt S) (Monad_arrSt S) (Eq1_RelSt S) (Eq1_arrSt S)
        (fun A => state_arrow_map S F unit A).
    Proof.
      constructor.
      - intros A x y H.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE (unit * S)%type
                        (A * S)%type _ _)).
        intros p r.
        etransitivity; [ exact (HF _ _ x p r) |].
        etransitivity; [ exact (H p r) |].
        symmetry. exact (HF _ _ y p r).
      - intros A a.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE (unit * S)%type
                        (A * S)%type _ _)).
        intros [u s] r.
        etransitivity; [ exact (HF _ _ _ (u, s) r) |].
        symmetry.
        exact (@rel_pure arr HA HR _ _ (fun '(_, s0) => (a, s0)) (u, s) r).
      - intros A B m k.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE (unit * S)%type
                        (B * S)%type _ _)).
        intros [u s] r.
        etransitivity; [ exact (HF _ _ _ (u, s) r) |].
        etransitivity;
          [ exact (@relS_bind Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel
                     RelArrowApply_Rel S unit A B m k u s r) |].
        etransitivity;
          [| symmetry;
             exact (@relS_bind arr HA HAA HR HRA S unit A B
                      (state_arrow_map S F unit A m)
                      (fun a => state_arrow_map S F unit B (k a)) u s r) ].
        split; intros [a [s' [H1 H2]]]; exists a, s'; split.
        + exact (proj2 (HF _ _ m (u, s) (a, s')) H1).
        + exact (proj2 (HF _ _ (k a) (u, s') r) H2).
        + exact (proj1 (HF _ _ m (u, s) (a, s')) H1).
        + exact (proj1 (HF _ _ (k a) (u, s') r) H2).
    Qed.

    Lemma ofRelStExc_morphism (S : Type) :
      @MonadMorphism (stateArrT S OR unit) (stateArrT S OA unit)
        (Monad_RelStExc S) (Monad_arrStExc S)
        (Eq1_RelStExc S) (Eq1_arrStExc S)
        (fun A => state_arrow_map S (option_arrow_map F) unit A).
    Proof.
      constructor.
      - intros A x y H.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE (unit * S)%type
                        (option (A * S)) _ _)).
        intros p o.
        etransitivity; [ exact (HF _ _ x p o) |].
        etransitivity; [ exact (H p o) |].
        symmetry. exact (HF _ _ y p o).
      - intros A a.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE (unit * S)%type
                        (option (A * S)) _ _)).
        intros [u s] o.
        etransitivity; [ exact (HF _ _ _ (u, s) o) |].
        etransitivity;
          [ exact (@relE_pure Rel Arrow_Rel RelArrow_Rel ArrowChoice_Rel
                     S unit A (fun _ => a) u s o) |].
        symmetry.
        exact (@relE_pure arr HA HR HC S unit A (fun _ => a) u s o).
      - intros A B m k.
        apply (proj2 (@rel_arrow_eq arr HA HE HR HRE (unit * S)%type
                        (option (B * S)) _ _)).
        intros [u s] o.
        etransitivity; [ exact (HF _ _ _ (u, s) o) |].
        etransitivity;
          [ exact (@relE_bind Rel Arrow_Rel ArrowApply_Rel RelArrow_Rel
                     RelArrowApply_Rel ArrowChoice_Rel RelArrowChoice_Rel
                     S unit A B m k u s o) |].
        etransitivity;
          [| symmetry;
             exact (@relE_bind arr HA HAA HR HRA HC HRC S unit A B
                      (state_arrow_map S (option_arrow_map F) unit A m)
                      (fun a => state_arrow_map S (option_arrow_map F) unit B (k a))
                      u s o) ].
        split; intros [o1 [H1 H2]]; exists o1; split.
        + exact (proj2 (HF _ _ m (u, s) o1) H1).
        + destruct o1 as [[a s']|];
            [ exact (proj2 (HF _ _ (k a) (u, s') o) H2) | exact H2 ].
        + exact (proj1 (HF _ _ m (u, s) o1) H1).
        + destruct o1 as [[a s']|];
            [ exact (proj1 (HF _ _ (k a) (u, s') o) H2) | exact H2 ].
    Qed.

    Theorem spPure_morphism_rel :
      @MonadMorphism divndNE (arr unit) Monad__divndNE Monad_arr0
        Eq1__divndNE Eq1_arr0 (fun A => @spPure A).
    Proof.
      exact (@MonadMorphism_comp divndNE (Rel unit) (arr unit)
               Monad__divndNE Monad_Rel0 Monad_arr0
               Eq1__divndNE Eq1_Rel0 Eq1_arr0
               (@Eq1Equivalence_Arrow arr HA HAA HE unit)
               (@termRel) (fun A => F unit A) termRel_morphism ofRel_morphism).
    Qed.

    Theorem spSt_morphism_rel (S : Type) :
      @MonadMorphism (stdivndNE S) (stateArrT S arr unit) (Monad__stdivndNE S)
        (Monad_arrSt S) (Eq1__stdivndNE S) (Eq1_arrSt S) (fun A => @spSt S A).
    Proof.
      exact (@MonadMorphism_comp (stdivndNE S) (stateArrT S Rel unit)
               (stateArrT S arr unit)
               (Monad__stdivndNE S) (Monad_RelSt S) (Monad_arrSt S)
               (Eq1__stdivndNE S) (Eq1_RelSt S) (Eq1_arrSt S)
               (@Eq1Equivalence_Arrow (stateArrT S arr)
                  (@Arrow_stateArrT S arr HA)
                  (@ArrowApply_stateArrT S arr HA HAA)
                  (@ArrowEq_stateArrT S arr HE) unit)
               (@termRelSt S) (fun A => state_arrow_map S F unit A)
               (termRelSt_morphism S) (ofRelSt_morphism S)).
    Qed.

    Theorem spStExc_morphism_rel (S : Type) :
      @MonadMorphism (stdivexcndNE S) (stateArrT S OA unit) (Monad__stdivexcndNE S)
        (Monad_arrStExc S) (Eq1__stdivexcndNE S) (Eq1_arrStExc S)
        (fun A => @spStExc S A).
    Proof.
      exact (@MonadMorphism_comp (stdivexcndNE S) (stateArrT S OR unit)
               (stateArrT S OA unit)
               (Monad__stdivexcndNE S) (Monad_RelStExc S) (Monad_arrStExc S)
               (Eq1__stdivexcndNE S) (Eq1_RelStExc S) (Eq1_arrStExc S)
               (@Eq1Equivalence_Arrow (stateArrT S OA)
                  (@Arrow_stateArrT S OA Arrow_OA)
                  (@ArrowApply_stateArrT S OA Arrow_OA Apply_OA)
                  (@ArrowEq_stateArrT S OA Eq_OA) unit)
               (@termRelStExc S)
               (fun A => state_arrow_map S (option_arrow_map F) unit A)
               (termRelStExc_morphism S) (ofRelStExc_morphism S)).
    Qed.
  End ByRelations.
End SPMorphisms.

(* ================================================================= *)
(** * The four SP readings at the three levels                        *)
(* ================================================================= *)

(** The judgement on a base arrow, at arbitrary indices: [X] is what a
    precondition is a predicate on, [Y] what a postcondition is. *)

Definition aspHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getASPArr (@relASP X Y R))) k P Q.

Definition dslpHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getDSLPArr (@relDSLP X Y R))) k P Q.

Definition dspHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getDSP (@dspOfRelArr X Y R))) k P Q.

Definition aslpHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getASLP (@aslpOfRelArr X Y R))) k P Q.

(** Each reading of a relation, spelled out. *)
Lemma aspHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getASPArr (relASP R) P y <-> exists x, P x /\ R x y.
Proof. reflexivity. Qed.

Lemma dslpHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getDSLPArr (relDSLP R) P y <-> forall x, R x y -> P x.
Proof. reflexivity. Qed.

Lemma dspHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getDSP (dspOfRelArr R) P y
  <-> (exists x, P x /\ R x y) /\ (forall x, R x y -> P x).
Proof. reflexivity. Qed.

Lemma aslpHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getASLP (aslpOfRelArr R) P y
  <-> (exists x, P x /\ R x y) \/ (forall x, R x y -> P x).
Proof. reflexivity. Qed.

(** ** ASP *)

Definition aspPure {A} (d : divndNE A) : ASP A := spPure (@relASP) d.
Definition aspSt {S A} (m : stdivndNE S A) : ASPSt S A := spSt (@relASP) m.
Definition aspStExc {S A} (m : stdivexcndNE S A) : ASPStExc S A :=
  spStExc (@relASP) m.

Lemma aspPure_morphism :
  @MonadMorphism divndNE ASP Monad__divndNE Monad_ASP
    Eq1__divndNE Eq1_ASP (@aspPure).
Proof.
  exact (spPure_morphism (@relASP) asp_from_rel_morphism
           ArrowLaws_PureASPostArr ArrowApplyLaws_PureASPostArr).
Qed.

Lemma aspSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (ASPSt S) (Monad__stdivndNE S) (Monad_ASPSt S)
    (Eq1__stdivndNE S) (Eq1_ASPSt S) (@aspSt S).
Proof.
  exact (spSt_morphism (@relASP) asp_from_rel_morphism
           ArrowLaws_PureASPostArr ArrowApplyLaws_PureASPostArr S).
Qed.

Lemma aspStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASPStExc S) (Monad__stdivexcndNE S) (Monad_ASPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASPStExc S) (@aspStExc S).
Proof.
  exact (spStExc_morphism (@relASP) asp_from_rel_morphism
           ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr
           ArrowApplyLaws_PureASPostArr S).
Qed.

(** The same three, through the relations denoted. *)
Lemma aspPure_morphism_rel :
  @MonadMorphism divndNE ASP Monad__divndNE Monad_ASP
    Eq1__divndNE Eq1_ASP (@aspPure).
Proof.
  exact (spPure_morphism_rel (@relASP) (fun A B R a b => aspRel_ofRel R a b)).
Qed.

Lemma aspSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (ASPSt S) (Monad__stdivndNE S) (Monad_ASPSt S)
    (Eq1__stdivndNE S) (Eq1_ASPSt S) (@aspSt S).
Proof.
  exact (spSt_morphism_rel (@relASP) (fun A B R a b => aspRel_ofRel R a b) S).
Qed.

Lemma aspStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASPStExc S) (Monad__stdivexcndNE S) (Monad_ASPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASPStExc S) (@aspStExc S).
Proof.
  exact (spStExc_morphism_rel (@relASP) (fun A B R a b => aspRel_ofRel R a b) S).
Qed.

#[global] Instance IsMonadMorphism_aspPure : IsMonadMorphism (@aspPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ aspPure_morphism_rel.
#[global] Instance IsMonadMorphism_aspSt (S : Type) :
  IsMonadMorphism (@aspSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aspSt_morphism_rel S).
#[global] Instance IsMonadMorphism_aspStExc (S : Type)
  : IsMonadMorphism (@aspStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aspStExc_morphism_rel S).

(** One base arrow, three pairs of indices. *)
Theorem triple_aspPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@aspPure) d k P Q
  <-> aspHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aspSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@aspSt S) m k P Q
  <-> aspHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aspStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@aspStExc S) m k P Q
  <-> aspHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(** ** DSLP *)

Definition dslpPure {A} (d : divndNE A) : DSLP A := spPure (@relDSLP) d.
Definition dslpSt {S A} (m : stdivndNE S A) : DSLPSt S A := spSt (@relDSLP) m.
Definition dslpStExc {S A} (m : stdivexcndNE S A) : DSLPStExc S A :=
  spStExc (@relDSLP) m.

Lemma dslpPure_morphism :
  @MonadMorphism divndNE DSLP Monad__divndNE Monad_DSLP
    Eq1__divndNE Eq1_DSLP (@dslpPure).
Proof.
  exact (spPure_morphism (@relDSLP) dslp_from_rel_morphism
           ArrowLaws_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr).
Qed.

Lemma dslpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DSLPSt S) (Monad__stdivndNE S) (Monad_DSLPSt S)
    (Eq1__stdivndNE S) (Eq1_DSLPSt S) (@dslpSt S).
Proof.
  exact (spSt_morphism (@relDSLP) dslp_from_rel_morphism
           ArrowLaws_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr S).
Qed.

Lemma dslpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSLPStExc S) (Monad__stdivexcndNE S) (Monad_DSLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSLPStExc S) (@dslpStExc S).
Proof.
  exact (spStExc_morphism (@relDSLP) dslp_from_rel_morphism
           ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr
           ArrowApplyLaws_PureDSLPostArr S).
Qed.

(** The same three, through the relations denoted. *)
Lemma dslpPure_morphism_rel :
  @MonadMorphism divndNE DSLP Monad__divndNE Monad_DSLP
    Eq1__divndNE Eq1_DSLP (@dslpPure).
Proof.
  exact (spPure_morphism_rel (@relDSLP) (fun A B R a b => dslpRel_ofRel R a b)).
Qed.

Lemma dslpSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (DSLPSt S) (Monad__stdivndNE S) (Monad_DSLPSt S)
    (Eq1__stdivndNE S) (Eq1_DSLPSt S) (@dslpSt S).
Proof.
  exact (spSt_morphism_rel (@relDSLP) (fun A B R a b => dslpRel_ofRel R a b) S).
Qed.

Lemma dslpStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSLPStExc S) (Monad__stdivexcndNE S) (Monad_DSLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSLPStExc S) (@dslpStExc S).
Proof.
  exact (spStExc_morphism_rel (@relDSLP) (fun A B R a b => dslpRel_ofRel R a b) S).
Qed.

#[global] Instance IsMonadMorphism_dslpPure : IsMonadMorphism (@dslpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dslpPure_morphism_rel.
#[global] Instance IsMonadMorphism_dslpSt (S : Type) :
  IsMonadMorphism (@dslpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dslpSt_morphism_rel S).
#[global] Instance IsMonadMorphism_dslpStExc (S : Type)
  : IsMonadMorphism (@dslpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dslpStExc_morphism_rel S).

(** One base arrow, three pairs of indices. *)
Theorem triple_dslpPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@dslpPure) d k P Q
  <-> dslpHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dslpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dslpSt S) m k P Q
  <-> dslpHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dslpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dslpStExc S) m k P Q
  <-> dslpHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(** ** DSP *)

Definition dspPure {A} (d : divndNE A) : DSP A := spPure (@dspOfRelArr) d.
Definition dspSt {S A} (m : stdivndNE S A) : DSPSt S A := spSt (@dspOfRelArr) m.
Definition dspStExc {S A} (m : stdivexcndNE S A) : DSPStExc S A :=
  spStExc (@dspOfRelArr) m.

Lemma dspPure_morphism :
  @MonadMorphism divndNE DSP Monad__divndNE Monad_DSP
    Eq1__divndNE Eq1_DSP (@dspPure).
Proof.
  exact (spPure_morphism (@dspOfRelArr) dsp_from_rel_morphism ArrowLaws_DSPArr
           ArrowApplyLaws_DSPArr).
Qed.

Lemma dspSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DSPSt S) (Monad__stdivndNE S) (Monad_DSPSt S)
    (Eq1__stdivndNE S) (Eq1_DSPSt S) (@dspSt S).
Proof.
  exact (spSt_morphism (@dspOfRelArr) dsp_from_rel_morphism
           ArrowLaws_DSPArr ArrowApplyLaws_DSPArr S).
Qed.

Lemma dspStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSPStExc S) (Monad__stdivexcndNE S) (Monad_DSPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSPStExc S) (@dspStExc S).
Proof.
  exact (spStExc_morphism (@dspOfRelArr) dsp_from_rel_morphism
           ArrowLaws_DSPArr ArrowChoiceLaws_DSPArr ArrowApplyLaws_DSPArr S).
Qed.

(** The same three, through the relations denoted. *)
Lemma dspPure_morphism_rel :
  @MonadMorphism divndNE DSP Monad__divndNE Monad_DSP
    Eq1__divndNE Eq1_DSP (@dspPure).
Proof.
  exact (spPure_morphism_rel (@dspOfRelArr) (fun A B R a b => dspRel_ofRelArr R a b)).
Qed.

Lemma dspSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (DSPSt S) (Monad__stdivndNE S) (Monad_DSPSt S)
    (Eq1__stdivndNE S) (Eq1_DSPSt S) (@dspSt S).
Proof.
  exact (spSt_morphism_rel (@dspOfRelArr) (fun A B R a b => dspRel_ofRelArr R a b) S).
Qed.

Lemma dspStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSPStExc S) (Monad__stdivexcndNE S) (Monad_DSPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSPStExc S) (@dspStExc S).
Proof.
  exact (spStExc_morphism_rel (@dspOfRelArr) (fun A B R a b => dspRel_ofRelArr R a b) S).
Qed.

#[global] Instance IsMonadMorphism_dspPure : IsMonadMorphism (@dspPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dspPure_morphism_rel.
#[global] Instance IsMonadMorphism_dspSt (S : Type) :
  IsMonadMorphism (@dspSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dspSt_morphism_rel S).
#[global] Instance IsMonadMorphism_dspStExc (S : Type)
  : IsMonadMorphism (@dspStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dspStExc_morphism_rel S).

(** One base arrow, three pairs of indices. *)
Theorem triple_dspPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@dspPure) d k P Q
  <-> dspHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dspSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dspSt S) m k P Q
  <-> dspHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dspStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dspStExc S) m k P Q
  <-> dspHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(** ** ASLP *)

Definition aslpPure {A} (d : divndNE A) : ASLP A := spPure (@aslpOfRelArr) d.
Definition aslpSt {S A} (m : stdivndNE S A) : ASLPSt S A := spSt (@aslpOfRelArr) m.
Definition aslpStExc {S A} (m : stdivexcndNE S A) : ASLPStExc S A :=
  spStExc (@aslpOfRelArr) m.

Lemma aslpPure_morphism :
  @MonadMorphism divndNE ASLP Monad__divndNE Monad_ASLP
    Eq1__divndNE Eq1_ASLP (@aslpPure).
Proof.
  exact (spPure_morphism (@aslpOfRelArr) aslp_from_rel_morphism
           ArrowLaws_ASLPArr ArrowApplyLaws_ASLPArr).
Qed.

Lemma aslpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (ASLPSt S) (Monad__stdivndNE S) (Monad_ASLPSt S)
    (Eq1__stdivndNE S) (Eq1_ASLPSt S) (@aslpSt S).
Proof.
  exact (spSt_morphism (@aslpOfRelArr) aslp_from_rel_morphism
           ArrowLaws_ASLPArr ArrowApplyLaws_ASLPArr S).
Qed.

Lemma aslpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASLPStExc S) (Monad__stdivexcndNE S) (Monad_ASLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASLPStExc S) (@aslpStExc S).
Proof.
  exact (spStExc_morphism (@aslpOfRelArr) aslp_from_rel_morphism
           ArrowLaws_ASLPArr ArrowChoiceLaws_ASLPArr ArrowApplyLaws_ASLPArr
           S).
Qed.

(** The same three, through the relations denoted. *)
Lemma aslpPure_morphism_rel :
  @MonadMorphism divndNE ASLP Monad__divndNE Monad_ASLP
    Eq1__divndNE Eq1_ASLP (@aslpPure).
Proof.
  exact (spPure_morphism_rel (@aslpOfRelArr) (fun A B R a b => aslpRel_ofRelArr R a b)).
Qed.

Lemma aslpSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (ASLPSt S) (Monad__stdivndNE S) (Monad_ASLPSt S)
    (Eq1__stdivndNE S) (Eq1_ASLPSt S) (@aslpSt S).
Proof.
  exact (spSt_morphism_rel (@aslpOfRelArr)
           (fun A B R a b => aslpRel_ofRelArr R a b) S).
Qed.

Lemma aslpStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASLPStExc S) (Monad__stdivexcndNE S) (Monad_ASLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASLPStExc S) (@aslpStExc S).
Proof.
  exact (spStExc_morphism_rel (@aslpOfRelArr)
           (fun A B R a b => aslpRel_ofRelArr R a b) S).
Qed.

#[global] Instance IsMonadMorphism_aslpPure : IsMonadMorphism (@aslpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ aslpPure_morphism_rel.
#[global] Instance IsMonadMorphism_aslpSt (S : Type) :
  IsMonadMorphism (@aslpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aslpSt_morphism_rel S).
#[global] Instance IsMonadMorphism_aslpStExc (S : Type)
  : IsMonadMorphism (@aslpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aslpStExc_morphism_rel S).

(** One base arrow, three pairs of indices. *)
Theorem triple_aslpPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@aslpPure) d k P Q
  <-> aslpHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aslpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@aslpSt S) m k P Q
  <-> aslpHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aslpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@aslpStExc S) m k P Q
  <-> aslpHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(* ================================================================= *)
(** * The twenty-four readings, in terms of the outcomes              *)
(* ================================================================= *)

(** What each reading says of a precondition or a postcondition, at
    the two stacks.  The WP ones hold by computation. *)

Section Readings.
  Context {S A : Type}.

  Lemma dwpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (dwpSt m) s) Q
    <-> forall o, outSt m s o -> match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma dwlpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (dwlpSt m) s) Q
    <-> forall o, outSt m s o -> match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma awpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (awpSt m) s) Q
    <-> exists o, outSt m s o /\ match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma awlpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (awlpSt m) s) Q
    <-> exists o, outSt m s o /\ match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma aspSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getASPArr (aspSt m) (fun p => P (snd p)) r
    <-> exists s, P s /\ outSt m s (Some r).
  Proof.
    split.
    - intros [[[] s] [Hp Hr]]. exists s. exact (conj Hp Hr).
    - intros [s [Hp Hr]]. exists (tt, s). exact (conj Hp Hr).
  Qed.

  Lemma dslpSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getDSLPArr (dslpSt m) (fun p => P (snd p)) r
    <-> forall s, outSt m s (Some r) -> P s.
  Proof.
    split.
    - intros H s Hr. exact (H (tt, s) Hr).
    - intros H [[] s] Hr. exact (H s Hr).
  Qed.

  Lemma dspSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getDSP (dspSt m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outSt m s (Some r))
        /\ (forall s, outSt m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] H]. split.
      + exists s. exact (conj Hp Hr).
      + intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] H]. split.
      + exists (tt, s). exact (conj Hp Hr).
      + intros [[] s'] Hr'. exact (H s' Hr').
  Qed.

  Lemma aslpSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getASLP (aslpSt m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outSt m s (Some r))
        \/ (forall s, outSt m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] | H].
      + left. exists s. exact (conj Hp Hr).
      + right. intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] | H].
      + left. exists (tt, s). exact (conj Hp Hr).
      + right. intros [[] s'] Hr'. exact (H s' Hr').
  Qed.

  Lemma dwpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (dwpStExc m) s)) Q
    <-> forall o, outStExc m s o -> match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma dwlpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (dwlpStExc m) s)) Q
    <-> forall o, outStExc m s o -> match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma awpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (awpStExc m) s)) Q
    <-> exists o, outStExc m s o /\ match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma awlpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (awlpStExc m) s)) Q
    <-> exists o, outStExc m s o /\ match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma aspStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getASPArr (aspStExc m) (fun p => P (snd p)) r
    <-> exists s, P s /\ outStExc m s (Some r).
  Proof.
    split.
    - intros [[[] s] [Hp Hr]]. exists s. exact (conj Hp Hr).
    - intros [s [Hp Hr]]. exists (tt, s). exact (conj Hp Hr).
  Qed.

  Lemma dslpStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getDSLPArr (dslpStExc m) (fun p => P (snd p)) r
    <-> forall s, outStExc m s (Some r) -> P s.
  Proof.
    split.
    - intros H s Hr. exact (H (tt, s) Hr).
    - intros H [[] s] Hr. exact (H s Hr).
  Qed.

  Lemma dspStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getDSP (dspStExc m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outStExc m s (Some r))
        /\ (forall s, outStExc m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] H]. split.
      + exists s. exact (conj Hp Hr).
      + intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] H]. split.
      + exists (tt, s). exact (conj Hp Hr).
      + intros [[] s'] Hr'. exact (H s' Hr').
  Qed.

  Lemma aslpStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getASLP (aslpStExc m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outStExc m s (Some r))
        \/ (forall s, outStExc m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] | H].
      + left. exists s. exact (conj Hp Hr).
      + right. intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] | H].
      + left. exists (tt, s). exact (conj Hp Hr).
      + right. intros [[] s'] Hr'. exact (H s' Hr').
  Qed.
End Readings.
