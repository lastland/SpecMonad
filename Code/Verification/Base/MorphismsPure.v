(** * The eight readings of the base computation monad

    Each predicate-transformer reading is defined once, at the base:

      WP   a monad morphism [divndNE ~> WPure]: [dwpPure], [dwlpPure],
           [awpPure], [awlpPure];

      SP   a base arrow morphism [F : Rel ~> arr] ([SP/SPostArrEquiv.v])
           applied to the relation between the start point and the
           terminating outcomes ([spPure F]): [aspPure], [dslpPure],
           [dspPure], [aslpPure].  An arrow morphism is a monad morphism at
           each fixed input ([arrow_morphism_monad]).

    Each has an [IsMonadMorphism] instance.  Their lifts are in
    [State/MorphismsSt.v] and [StateExc/MorphismsStExc.v].  At the input
    [unit] DSP coincides with ASP and ASLP with DSLP ([DSPMonad.v],
    [ASLPMonad.v]); what tells the four apart is the base arrow at an
    arbitrary input. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import
  Arrow OptionArrowT StateArrowT ArrowMonad ArrowMorphism RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Relational Require Import
  Rel RelSPostArr.
From Incorrectness.SP Require Import
  SPostArr DSPASLPArr SPostArrEquiv.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Relational Require PredMonad RelMonads.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Base Require Import DivNonDetNE.


Local Notation Pred := PredMonad.PredM.Pred.
Local Notation Monad_Pred := PredMonad.PredM.Monad_Pred.
Local Notation Eq1_Pred := PredMonad.PredM.Eq1_Pred.
Local Notation Eq1Equivalence_Pred := PredMonad.PredMFacts.Eq1Equivalence_Pred.
Local Notation MonadLawsE_Pred := PredMonad.PredMFacts.MonadLawsE_Pred.

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

(** The four readings at the three levels, each a monad morphism. *)

Lemma dwpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@dwpPure).
Proof. exact (demonicWP_morphism False). Qed.

#[global] Instance IsMonadMorphism_dwpPure : IsMonadMorphism (@dwpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dwpPure_morphism.

Lemma dwlpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@dwlpPure).
Proof. exact (demonicWP_morphism True). Qed.

#[global] Instance IsMonadMorphism_dwlpPure : IsMonadMorphism (@dwlpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dwlpPure_morphism.

Lemma awpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@awpPure).
Proof. exact (angelicWP_morphism False). Qed.

#[global] Instance IsMonadMorphism_awpPure : IsMonadMorphism (@awpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ awpPure_morphism.

Lemma awlpPure_morphism :
  @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
    Eq1__divndNE Eq1_WPure (@awlpPure).
Proof. exact (angelicWP_morphism True). Qed.

#[global] Instance IsMonadMorphism_awlpPure : IsMonadMorphism (@awlpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ awlpPure_morphism.

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

Definition termRel {A} (d : divndNE A) : Rel unit A :=
  outcomes0 (sliceNE d).

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

  (** All three are [F] at one relation each: the arrow transformers change
      the indices and nothing else. *)
  Lemma spPure_unfold {A} (d : divndNE A) :
    spPure d = F unit A (fun _ a => unOptionT (getNE d) (Some a)).
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
  End ByRelations.
End SPMorphisms.

(* ================================================================= *)
(** * The four SP readings at the three levels                        *)
(* ================================================================= *)

(** ** ASP *)

Definition aspPure {A} (d : divndNE A) : ASP A := spPure (@relASP) d.

Lemma aspPure_morphism :
  @MonadMorphism divndNE ASP Monad__divndNE Monad_ASP
    Eq1__divndNE Eq1_ASP (@aspPure).
Proof.
  exact (spPure_morphism (@relASP) asp_from_rel_morphism
           ArrowLaws_PureASPostArr ArrowApplyLaws_PureASPostArr).
Qed.

(** The same three, through the relations denoted. *)
Lemma aspPure_morphism_rel :
  @MonadMorphism divndNE ASP Monad__divndNE Monad_ASP
    Eq1__divndNE Eq1_ASP (@aspPure).
Proof.
  exact (spPure_morphism_rel (@relASP) (fun A B R a b => aspRel_ofRel R a b)).
Qed.

#[global] Instance IsMonadMorphism_aspPure : IsMonadMorphism (@aspPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ aspPure_morphism_rel.

(** ** DSLP *)

Definition dslpPure {A} (d : divndNE A) : DSLP A := spPure (@relDSLP) d.

Lemma dslpPure_morphism :
  @MonadMorphism divndNE DSLP Monad__divndNE Monad_DSLP
    Eq1__divndNE Eq1_DSLP (@dslpPure).
Proof.
  exact (spPure_morphism (@relDSLP) dslp_from_rel_morphism
           ArrowLaws_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr).
Qed.

(** The same three, through the relations denoted. *)
Lemma dslpPure_morphism_rel :
  @MonadMorphism divndNE DSLP Monad__divndNE Monad_DSLP
    Eq1__divndNE Eq1_DSLP (@dslpPure).
Proof.
  exact (spPure_morphism_rel (@relDSLP) (fun A B R a b => dslpRel_ofRel R a b)).
Qed.

#[global] Instance IsMonadMorphism_dslpPure : IsMonadMorphism (@dslpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dslpPure_morphism_rel.

(** ** DSP *)

Definition dspPure {A} (d : divndNE A) : DSP A := spPure (@dspOfRelArr) d.

Lemma dspPure_morphism :
  @MonadMorphism divndNE DSP Monad__divndNE Monad_DSP
    Eq1__divndNE Eq1_DSP (@dspPure).
Proof.
  exact (spPure_morphism (@dspOfRelArr) dsp_from_rel_morphism ArrowLaws_DSPArr
           ArrowApplyLaws_DSPArr).
Qed.

(** The same three, through the relations denoted. *)
Lemma dspPure_morphism_rel :
  @MonadMorphism divndNE DSP Monad__divndNE Monad_DSP
    Eq1__divndNE Eq1_DSP (@dspPure).
Proof.
  exact (spPure_morphism_rel (@dspOfRelArr) (fun A B R a b => dspRel_ofRelArr R a b)).
Qed.

#[global] Instance IsMonadMorphism_dspPure : IsMonadMorphism (@dspPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ dspPure_morphism_rel.

(** ** ASLP *)

Definition aslpPure {A} (d : divndNE A) : ASLP A := spPure (@aslpOfRelArr) d.

Lemma aslpPure_morphism :
  @MonadMorphism divndNE ASLP Monad__divndNE Monad_ASLP
    Eq1__divndNE Eq1_ASLP (@aslpPure).
Proof.
  exact (spPure_morphism (@aslpOfRelArr) aslp_from_rel_morphism
           ArrowLaws_ASLPArr ArrowApplyLaws_ASLPArr).
Qed.

(** The same three, through the relations denoted. *)
Lemma aslpPure_morphism_rel :
  @MonadMorphism divndNE ASLP Monad__divndNE Monad_ASLP
    Eq1__divndNE Eq1_ASLP (@aslpPure).
Proof.
  exact (spPure_morphism_rel (@aslpOfRelArr) (fun A B R a b => aslpRel_ofRelArr R a b)).
Qed.

#[global] Instance IsMonadMorphism_aslpPure : IsMonadMorphism (@aslpPure) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ aslpPure_morphism_rel.
