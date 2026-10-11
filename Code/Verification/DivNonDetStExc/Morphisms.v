(** * The eight readings with state and exceptions, as lifts of the base ones

    WP   a base morphism [σ] lifts to
         [stateT_map S (optionT_map σ) : stdivexcndNE S ~> WStExc S]
         ([wpStExc_morphism]); [dwpStExc] &c. are the lifts of [dwpPure] &c.

    SP   a base arrow morphism [F] lifts through
         [state_option_arrow_morphism] ([spStExc F], [spStExc_morphism],
         [spStExc_morphism_rel]); [aspStExc] &c. are its instances.

    Each has an [IsMonadMorphism] instance. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import
  Arrow OptionArrowT StateArrowT RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Relational Require Import
  Rel.
From Incorrectness.SP Require Import
  SPostArrEquiv.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.

From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.

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

(** A base morphism into [WPure], under [stateT], and under [stateT] over
    [optionT]. *)
Section LiftedWP.
  Variable σ : forall A, divndNE A -> WPure A.
  Hypothesis Hσ :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure σ.
  Variable S : Type.

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

End LiftedWP.
Definition dwpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@dwpPure)) A m.

Lemma dwpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@dwpStExc S).
Proof. exact (wpStExc_morphism (@dwpPure) dwpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_dwpStExc (S : Type)
  : IsMonadMorphism (@dwpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwpStExc_morphism S).
Definition dwlpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@dwlpPure)) A m.

Lemma dwlpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@dwlpStExc S).
Proof. exact (wpStExc_morphism (@dwlpPure) dwlpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_dwlpStExc (S : Type)
  : IsMonadMorphism (@dwlpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwlpStExc_morphism S).
Definition awpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@awpPure)) A m.

Lemma awpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@awpStExc S).
Proof. exact (wpStExc_morphism (@awpPure) awpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_awpStExc (S : Type)
  : IsMonadMorphism (@awpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awpStExc_morphism S).
Definition awlpStExc {S A} (m : stdivexcndNE S A) : WStExc S A :=
  stateT_map S (optionT_map (@awlpPure)) A m.

Lemma awlpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (WStExc S) (Monad__stdivexcndNE S) (Monad__WStExc S)
    (Eq1__stdivexcndNE S) (Eq1__WStExc S) (@awlpStExc S).
Proof. exact (wpStExc_morphism (@awlpPure) awlpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_awlpStExc (S : Type)
  : IsMonadMorphism (@awlpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awlpStExc_morphism S).
Definition outcomesStExc {S A} (m : stateT S (optionT Pred) A)
  : stateArrT S (optionArrT Rel) unit A :=
  fun us o => unOptionT (runStateT m (snd us)) o.

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
Definition termRelStExc {S A} (m : stdivexcndNE S A) : stateArrT S OR unit A :=
  outcomesStExc (stateT_map S (optionT_map (@sliceNE)) A m).

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

  Definition spStExc {S A} (m : stdivexcndNE S A) : stateArrT S OA unit A :=
    state_arrow_map S (option_arrow_map F) unit A (termRelStExc m).

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
Definition aspStExc {S A} (m : stdivexcndNE S A) : ASPStExc S A :=
  spStExc (@relASP) m.

Lemma aspStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASPStExc S) (Monad__stdivexcndNE S) (Monad_ASPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASPStExc S) (@aspStExc S).
Proof.
  exact (spStExc_morphism (@relASP) asp_from_rel_morphism
           ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr
           ArrowApplyLaws_PureASPostArr S).
Qed.

Lemma aspStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASPStExc S) (Monad__stdivexcndNE S) (Monad_ASPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASPStExc S) (@aspStExc S).
Proof.
  exact (spStExc_morphism_rel (@relASP) (fun A B R a b => aspRel_ofRel R a b) S).
Qed.
#[global] Instance IsMonadMorphism_aspStExc (S : Type)
  : IsMonadMorphism (@aspStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aspStExc_morphism_rel S).
Definition dslpStExc {S A} (m : stdivexcndNE S A) : DSLPStExc S A :=
  spStExc (@relDSLP) m.

Lemma dslpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSLPStExc S) (Monad__stdivexcndNE S) (Monad_DSLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSLPStExc S) (@dslpStExc S).
Proof.
  exact (spStExc_morphism (@relDSLP) dslp_from_rel_morphism
           ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr
           ArrowApplyLaws_PureDSLPostArr S).
Qed.

Lemma dslpStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSLPStExc S) (Monad__stdivexcndNE S) (Monad_DSLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSLPStExc S) (@dslpStExc S).
Proof.
  exact (spStExc_morphism_rel (@relDSLP) (fun A B R a b => dslpRel_ofRel R a b) S).
Qed.
#[global] Instance IsMonadMorphism_dslpStExc (S : Type)
  : IsMonadMorphism (@dslpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dslpStExc_morphism_rel S).
Definition dspStExc {S A} (m : stdivexcndNE S A) : DSPStExc S A :=
  spStExc (@dspOfRelArr) m.

Lemma dspStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSPStExc S) (Monad__stdivexcndNE S) (Monad_DSPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSPStExc S) (@dspStExc S).
Proof.
  exact (spStExc_morphism (@dspOfRelArr) dsp_from_rel_morphism
           ArrowLaws_DSPArr ArrowChoiceLaws_DSPArr ArrowApplyLaws_DSPArr S).
Qed.

Lemma dspStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (DSPStExc S) (Monad__stdivexcndNE S) (Monad_DSPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_DSPStExc S) (@dspStExc S).
Proof.
  exact (spStExc_morphism_rel (@dspOfRelArr) (fun A B R a b => dspRel_ofRelArr R a b) S).
Qed.
#[global] Instance IsMonadMorphism_dspStExc (S : Type)
  : IsMonadMorphism (@dspStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dspStExc_morphism_rel S).
Definition aslpStExc {S A} (m : stdivexcndNE S A) : ASLPStExc S A :=
  spStExc (@aslpOfRelArr) m.

Lemma aslpStExc_morphism (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASLPStExc S) (Monad__stdivexcndNE S) (Monad_ASLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASLPStExc S) (@aslpStExc S).
Proof.
  exact (spStExc_morphism (@aslpOfRelArr) aslp_from_rel_morphism
           ArrowLaws_ASLPArr ArrowChoiceLaws_ASLPArr ArrowApplyLaws_ASLPArr
           S).
Qed.

Lemma aslpStExc_morphism_rel (S : Type) :
  @MonadMorphism (stdivexcndNE S) (ASLPStExc S) (Monad__stdivexcndNE S) (Monad_ASLPStExc S)
    (Eq1__stdivexcndNE S) (Eq1_ASLPStExc S) (@aslpStExc S).
Proof.
  exact (spStExc_morphism_rel (@aslpOfRelArr)
           (fun A B R a b => aslpRel_ofRelArr R a b) S).
Qed.
#[global] Instance IsMonadMorphism_aslpStExc (S : Type)
  : IsMonadMorphism (@aslpStExc S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aslpStExc_morphism_rel S).
