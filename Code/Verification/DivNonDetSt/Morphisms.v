(** * The eight readings with state, as lifts of the base ones

    WP   a base morphism [σ : divndNE ~> WPure] lifts to
         [stateT_map S σ : stdivndNE S ~> WSt S] ([wpSt_morphism], by
         [MonadMorphism_stateT]); [dwpSt] &c. are the lifts of [dwpPure] &c.

    SP   a base arrow morphism [F] lifts through [state_arrow_morphism]
         ([spSt F], [spSt_morphism]; and through the relations denoted,
         [spSt_morphism_rel]); [aspSt] &c. are its instances.

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
  WPure WPVariants.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.

From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.

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

  Theorem wpSt_morphism :
    @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
      (Eq1__stdivndNE S) (Eq1__WSt S) (stateT_map S σ).
  Proof.
    exact (@MonadMorphism_stateT divndNE WPure Monad__divndNE Monad_WPure
             Eq1__divndNE Eq1_WPure Eq1Equivalence_WPure MonadLawsE_WPure
             S σ Hσ).
  Qed.

End LiftedWP.

Definition dwpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@dwpPure) A m.

Lemma dwpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@dwpSt S).
Proof. exact (wpSt_morphism (@dwpPure) dwpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_dwpSt (S : Type) :
  IsMonadMorphism (@dwpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwpSt_morphism S).

Definition dwpSt_DWPSt {S A} (m : stdivndNE S A) : DWPSt S A := stateT_map S (@dwpPure_DWP) A m.

Lemma dwpSt_DWPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DWPSt S) (Monad__stdivndNE S) (Monad_DWPSt S)
    (Eq1__stdivndNE S) (Eq1_DWPSt S) (@dwpSt_DWPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE DWP Monad__divndNE Monad_DWP
           Eq1__divndNE Eq1_DWP Eq1Equivalence_DWP MonadLawsE_DWP
           S (@dwpPure_DWP) dwpPure_DWP_morphism).
Qed.

Definition dwlpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@dwlpPure) A m.

Lemma dwlpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@dwlpSt S).
Proof. exact (wpSt_morphism (@dwlpPure) dwlpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_dwlpSt (S : Type) :
  IsMonadMorphism (@dwlpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dwlpSt_morphism S).

Definition dwlpSt_DWLPSt {S A} (m : stdivndNE S A) : DWLPSt S A := stateT_map S (@dwlpPure_DWLP) A m.

Lemma dwlpSt_DWLPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DWLPSt S) (Monad__stdivndNE S) (Monad_DWLPSt S)
    (Eq1__stdivndNE S) (Eq1_DWLPSt S) (@dwlpSt_DWLPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE DWLP Monad__divndNE Monad_DWLP
           Eq1__divndNE Eq1_DWLP Eq1Equivalence_DWLP MonadLawsE_DWLP
           S (@dwlpPure_DWLP) dwlpPure_DWLP_morphism).
Qed.

Definition awpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@awpPure) A m.

Lemma awpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@awpSt S).
Proof. exact (wpSt_morphism (@awpPure) awpPure_morphism S). Qed.
#[global] Instance IsMonadMorphism_awpSt (S : Type) :
  IsMonadMorphism (@awpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awpSt_morphism S).

Definition awpSt_AWPSt {S A} (m : stdivndNE S A) : AWPSt S A := stateT_map S (@awpPure_AWP) A m.

Lemma awpSt_AWPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (AWPSt S) (Monad__stdivndNE S) (Monad_AWPSt S)
    (Eq1__stdivndNE S) (Eq1_AWPSt S) (@awpSt_AWPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE AWP Monad__divndNE Monad_AWP
           Eq1__divndNE Eq1_AWP Eq1Equivalence_AWP MonadLawsE_AWP
           S (@awpPure_AWP) awpPure_AWP_morphism).
Qed.

Definition awlpSt {S A} (m : stdivndNE S A) : WSt S A :=
  stateT_map S (@awlpPure) A m.

Lemma awlpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (WSt S) (Monad__stdivndNE S) (Monad__WSt S)
    (Eq1__stdivndNE S) (Eq1__WSt S) (@awlpSt S).
Proof. exact (wpSt_morphism (@awlpPure) awlpPure_morphism S). Qed.

#[global] Instance IsMonadMorphism_awlpSt (S : Type) :
  IsMonadMorphism (@awlpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (awlpSt_morphism S).

Definition awlpSt_AWLPSt {S A} (m : stdivndNE S A) : AWLPSt S A := stateT_map S (@awlpPure_AWLP) A m.

Lemma awlpSt_AWLPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (AWLPSt S) (Monad__stdivndNE S) (Monad_AWLPSt S)
    (Eq1__stdivndNE S) (Eq1_AWLPSt S) (@awlpSt_AWLPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE AWLP Monad__divndNE Monad_AWLP
           Eq1__divndNE Eq1_AWLP Eq1Equivalence_AWLP MonadLawsE_AWLP
           S (@awlpPure_AWLP) awlpPure_AWLP_morphism).
Qed.

(** Completeness lifts pointwise: [stateT] is a function space and its
    [eq1] is pointwise, so applying the base construction at each start
    state suffices.  Every element of a refined stateful monad is therefore
    the reading of a stateful computation. *)

Definition dwpProgramSt {S A} (w : DWPSt S A) : stdivndNE S A :=
  mkStateT (fun s => dwpProgram (runStateT w s)).

Theorem dwpSt_DWPSt_complete {S A} (w : DWPSt S A) :
  eq1 (dwpSt_DWPSt (dwpProgramSt w)) w.
Proof. intro s. exact (dwpPure_DWP_complete (runStateT w s)). Qed.

Definition dwlpProgramSt {S A} (w : DWLPSt S A) : stdivndNE S A :=
  mkStateT (fun s => dwlpProgram (runStateT w s)).

Theorem dwlpSt_DWLPSt_complete {S A} (w : DWLPSt S A) :
  eq1 (dwlpSt_DWLPSt (dwlpProgramSt w)) w.
Proof. intro s. exact (dwlpPure_DWLP_complete (runStateT w s)). Qed.

Definition awpProgramSt {S A} (w : AWPSt S A) : stdivndNE S A :=
  mkStateT (fun s => awpProgram (runStateT w s)).

Theorem awpSt_AWPSt_complete {S A} (w : AWPSt S A) :
  eq1 (awpSt_AWPSt (awpProgramSt w)) w.
Proof. intro s. exact (awpPure_AWP_complete (runStateT w s)). Qed.

Definition awlpProgramSt {S A} (w : AWLPSt S A) : stdivndNE S A :=
  mkStateT (fun s => awlpProgram (runStateT w s)).

Theorem awlpSt_AWLPSt_complete {S A} (w : AWLPSt S A) :
  eq1 (awlpSt_AWLPSt (awlpProgramSt w)) w.
Proof. intro s. exact (awlpPure_AWLP_complete (runStateT w s)). Qed.

Definition outcomesSt {S A} (m : stateT S Pred A) : stateArrT S Rel unit A :=
  fun us r => runStateT m (snd us) r.

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
Definition termRelSt {S A} (m : stdivndNE S A) : stateArrT S Rel unit A :=
  outcomesSt (stateT_map S (@sliceNE) A m).

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

  Definition spSt {S A} (m : stdivndNE S A) : stateArrT S arr unit A :=
    state_arrow_map S F unit A (termRelSt m).

  Lemma spSt_unfold {S A} (m : stdivndNE S A) :
    spSt m
    = F (unit * S)%type (A * S)%type (fun us r => outSt m (snd us) (Some r)).
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
  End ByRelations.
End SPMorphisms.
Definition aspSt {S A} (m : stdivndNE S A) : ASPSt S A := spSt (@relASP) m.

Lemma aspSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (ASPSt S) (Monad__stdivndNE S) (Monad_ASPSt S)
    (Eq1__stdivndNE S) (Eq1_ASPSt S) (@aspSt S).
Proof.
  exact (spSt_morphism (@relASP) asp_from_rel_morphism
           ArrowLaws_PureASPostArr ArrowApplyLaws_PureASPostArr S).
Qed.

Lemma aspSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (ASPSt S) (Monad__stdivndNE S) (Monad_ASPSt S)
    (Eq1__stdivndNE S) (Eq1_ASPSt S) (@aspSt S).
Proof.
  exact (spSt_morphism_rel (@relASP) (fun A B R a b => aspRel_ofRel R a b) S).
Qed.
#[global] Instance IsMonadMorphism_aspSt (S : Type) :
  IsMonadMorphism (@aspSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aspSt_morphism_rel S).
Definition dslpSt {S A} (m : stdivndNE S A) : DSLPSt S A := spSt (@relDSLP) m.

Lemma dslpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DSLPSt S) (Monad__stdivndNE S) (Monad_DSLPSt S)
    (Eq1__stdivndNE S) (Eq1_DSLPSt S) (@dslpSt S).
Proof.
  exact (spSt_morphism (@relDSLP) dslp_from_rel_morphism
           ArrowLaws_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr S).
Qed.

Lemma dslpSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (DSLPSt S) (Monad__stdivndNE S) (Monad_DSLPSt S)
    (Eq1__stdivndNE S) (Eq1_DSLPSt S) (@dslpSt S).
Proof.
  exact (spSt_morphism_rel (@relDSLP) (fun A B R a b => dslpRel_ofRel R a b) S).
Qed.
#[global] Instance IsMonadMorphism_dslpSt (S : Type) :
  IsMonadMorphism (@dslpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dslpSt_morphism_rel S).
Definition dspSt {S A} (m : stdivndNE S A) : DSPSt S A := spSt (@dspOfRelArr) m.

Lemma dspSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DSPSt S) (Monad__stdivndNE S) (Monad_DSPSt S)
    (Eq1__stdivndNE S) (Eq1_DSPSt S) (@dspSt S).
Proof.
  exact (spSt_morphism (@dspOfRelArr) dsp_from_rel_morphism
           ArrowLaws_DSPArr ArrowApplyLaws_DSPArr S).
Qed.

Lemma dspSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (DSPSt S) (Monad__stdivndNE S) (Monad_DSPSt S)
    (Eq1__stdivndNE S) (Eq1_DSPSt S) (@dspSt S).
Proof.
  exact (spSt_morphism_rel (@dspOfRelArr) (fun A B R a b => dspRel_ofRelArr R a b) S).
Qed.
#[global] Instance IsMonadMorphism_dspSt (S : Type) :
  IsMonadMorphism (@dspSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (dspSt_morphism_rel S).
Definition aslpSt {S A} (m : stdivndNE S A) : ASLPSt S A := spSt (@aslpOfRelArr) m.

Lemma aslpSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (ASLPSt S) (Monad__stdivndNE S) (Monad_ASLPSt S)
    (Eq1__stdivndNE S) (Eq1_ASLPSt S) (@aslpSt S).
Proof.
  exact (spSt_morphism (@aslpOfRelArr) aslp_from_rel_morphism
           ArrowLaws_ASLPArr ArrowApplyLaws_ASLPArr S).
Qed.

Lemma aslpSt_morphism_rel (S : Type) :
  @MonadMorphism (stdivndNE S) (ASLPSt S) (Monad__stdivndNE S) (Monad_ASLPSt S)
    (Eq1__stdivndNE S) (Eq1_ASLPSt S) (@aslpSt S).
Proof.
  exact (spSt_morphism_rel (@aslpOfRelArr)
           (fun A B R a b => aslpRel_ofRelArr R a b) S).
Qed.
#[global] Instance IsMonadMorphism_aslpSt (S : Type) :
  IsMonadMorphism (@aslpSt S) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ (aslpSt_morphism_rel S).

(* ================================================================= *)
(** * The readings of programs                                        *)
(* ================================================================= *)

(** A reading of a program is the reading of its denotation,
    [θ ∘ₘₘ denoteSt]: a monad morphism by composition, for any events [E]
    with answers. *)

Section ProgramReadings.
  Context {E : Type -> Type} `{HE : HasAnswers E} (S : Type).

  #[global] Instance IsMonadMorphism_dwpSt_denoteSt :
    IsMonadMorphism (@dwpSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := Eq1Equivalence__WSt S)
      (@denoteSt_morphism E HE S) (dwpSt_morphism S).

  #[global] Instance IsMonadMorphism_dwlpSt_denoteSt :
    IsMonadMorphism (@dwlpSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := Eq1Equivalence__WSt S)
      (@denoteSt_morphism E HE S) (dwlpSt_morphism S).

  #[global] Instance IsMonadMorphism_awpSt_denoteSt :
    IsMonadMorphism (@awpSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := Eq1Equivalence__WSt S)
      (@denoteSt_morphism E HE S) (awpSt_morphism S).

  #[global] Instance IsMonadMorphism_awlpSt_denoteSt :
    IsMonadMorphism (@awlpSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := Eq1Equivalence__WSt S)
      (@denoteSt_morphism E HE S) (awlpSt_morphism S).

  #[global] Instance IsMonadMorphism_aspSt_denoteSt :
    IsMonadMorphism (@aspSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := Eq1Equivalence_ASPSt S)
      (@denoteSt_morphism E HE S) (aspSt_morphism S).

  #[global] Instance IsMonadMorphism_dslpSt_denoteSt :
    IsMonadMorphism (@dslpSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := Eq1Equivalence_DSLPSt S)
      (@denoteSt_morphism E HE S) (dslpSt_morphism S).

  #[global] Instance IsMonadMorphism_dspSt_denoteSt :
    IsMonadMorphism (@dspSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := @Eq1Equivalence_Arrow (DSPStArr S) _ _ (ArrowEq_DSPStArr S) unit)
      (@denoteSt_morphism E HE S) (dspSt_morphism S).

  #[global] Instance IsMonadMorphism_aslpSt_denoteSt :
    IsMonadMorphism (@aslpSt S ∘ₘₘ @denoteSt E HE S) :=
    IsMonadMorphism_comp (EqW := @Eq1Equivalence_Arrow (ASLPStArr S) _ _ (ArrowEq_ASLPStArr S) unit)
      (@denoteSt_morphism E HE S) (aslpSt_morphism S).
End ProgramReadings.
