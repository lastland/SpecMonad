(** * Exceptions alone do not separate DSP from ASP, nor ASLP from DSLP
      (paper, Section 4.4)

    [DSPExc], [ASPExc], [ASLPExc] and [DSLPExc] are the monads of the option
    arrow transformer over the four base SP arrows, at input [unit].  Since
    [optionArrT arr unit A] is [arr unit (option A)], the collapse maps of
    [DSPMonad.v] and [ASLPMonad.v] at [option A] are maps between them,
    mutually inverse there ([asp_to_dsp_to_asp] &c.), and monad morphisms
    both ways ([dspExc_to_aspExc_morphism], [aspExc_to_dspExc_morphism],
    [aslpExc_to_dslpExc_morphism], [dslpExc_to_aslpExc_morphism]).  All four
    are specification monads ([OrderedMonad_DSPExc], [OrderedMonad_ASLPExc]),
    unlike their stateful versions: the flavours are told apart only when a
    result is reachable from two inputs, which state provides.

    The proof is generic: any family of maps preserving the relation denoted
    is a monad morphism of the option arrow transformer
    ([MonadMorphism_optionArrT_rel]), by [relO_bind]
    ([Lib/Arrow/RelArrowCoherence.v]).  The statements about DSP and ASLP
    elements are classical. *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT ArrowMonad RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.SP Require Import
  SPostArr DSPASLPArr ASPMonad DSLPMonad DSPMonad ASLPMonad.

(* ================================================================= *)
(** ** Maps that preserve the relation denoted are monad morphisms    *)
(* ================================================================= *)

Section OptionMorphism.
  Context {arr1 : Type -> Type -> Type}
    {HA1 : Arrow arr1} {HC1 : @ArrowChoice arr1 HA1} {HAA1 : @ArrowApply arr1 HA1}
    {HE1 : ArrowEq arr1}
    {HR1 : @RelArrow arr1 HA1} {HRC1 : @RelArrowChoice arr1 HA1 HC1 HR1}
    {HRA1 : @RelArrowApply arr1 HA1 HAA1 HR1} {HRE1 : @RelArrowEq arr1 HA1 HE1 HR1}.
  Context {arr2 : Type -> Type -> Type}
    {HA2 : Arrow arr2} {HC2 : @ArrowChoice arr2 HA2} {HAA2 : @ArrowApply arr2 HA2}
    {HE2 : ArrowEq arr2}
    {HR2 : @RelArrow arr2 HA2} {HRC2 : @RelArrowChoice arr2 HA2 HC2 HR2}
    {HRA2 : @RelArrowApply arr2 HA2 HAA2 HR2} {HRE2 : @RelArrowEq arr2 HA2 HE2 HR2}.

  Local Notation R1 := (@rel_reading arr1 HA1 HR1).
  Local Notation R2 := (@rel_reading arr2 HA2 HR2).

  Theorem MonadMorphism_optionArrT_rel (I : Type)
      (σ : forall A, arr1 I (option A) -> arr2 I (option A)) :
    (forall A m x o, R2 (σ A m) x o <-> R1 m x o) ->
    @MonadMorphism (optionArrT arr1 I) (optionArrT arr2 I)
      (@Monad_Arrow (optionArrT arr1) (@Arrow_optionArrT arr1 HA1 HC1)
         (@ArrowApply_optionArrT arr1 HA1 HC1 HAA1) I)
      (@Monad_Arrow (optionArrT arr2) (@Arrow_optionArrT arr2 HA2 HC2)
         (@ArrowApply_optionArrT arr2 HA2 HC2 HAA2) I)
      (@Eq1_Arrow (optionArrT arr1) (@ArrowEq_optionArrT arr1 HE1) I)
      (@Eq1_Arrow (optionArrT arr2) (@ArrowEq_optionArrT arr2 HE2) I)
      σ.
  Proof.
    intro Hσ. constructor.
    - intros A x y H.
      apply (proj2 (@rel_arrow_eq arr2 HA2 HE2 HR2 HRE2 I (option A) (σ A x) (σ A y))).
      intros i o. rewrite !Hσ.
      exact (proj1 (@rel_arrow_eq arr1 HA1 HE1 HR1 HRE1 I (option A) x y) H i o).
    - intros A a.
      apply (proj2 (@rel_arrow_eq arr2 HA2 HE2 HR2 HRE2 I (option A) _ _)).
      intros i o. rewrite Hσ.
      cbn [ret Monad_Arrow].
      rewrite (@relO_ret arr1 HA1 HR1 HC1), (@relO_ret arr2 HA2 HR2 HC2).
      reflexivity.
    - intros A B x k.
      apply (proj2 (@rel_arrow_eq arr2 HA2 HE2 HR2 HRE2 I (option B) _ _)).
      intros i o. rewrite Hσ.
      cbn [bind Monad_Arrow].
      rewrite (@relO_bind arr1 HA1 HAA1 HR1 HRA1 HC1 HRC1),
              (@relO_bind arr2 HA2 HAA2 HR2 HRA2 HC2 HRC2).
      split; intros [o1 [H1 H2]]; exists o1; split.
      + exact (proj2 (Hσ A x i o1) H1).
      + destruct o1 as [a|]; [ exact (proj2 (Hσ B (k a) i o) H2) | exact H2 ].
      + exact (proj1 (Hσ A x i o1) H1).
      + destruct o1 as [a|]; [ exact (proj1 (Hσ B (k a) i o) H2) | exact H2 ].
  Qed.
End OptionMorphism.

(* ================================================================= *)
(** ** The four exception monads                                      *)
(* ================================================================= *)

Definition ASPExc (A : Type) : Type := optionArrT ASPArr unit A.
#[global] Instance Monad_ASPExc : Monad ASPExc :=
  @Monad_Arrow (optionArrT ASPArr) (@Arrow_optionArrT ASPArr Arrow_ASPArr ArrowChoice_ASPArr)
    (@ArrowApply_optionArrT ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr) unit.
#[global] Instance Eq1_ASPExc : Eq1 ASPExc :=
  @Eq1_Arrow (optionArrT ASPArr) (@ArrowEq_optionArrT ASPArr ArrowEq_ASPArr) unit.

Definition DSLPExc (A : Type) : Type := optionArrT DSLPArr unit A.
#[global] Instance Monad_DSLPExc : Monad DSLPExc :=
  @Monad_Arrow (optionArrT DSLPArr) (@Arrow_optionArrT DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr)
    (@ArrowApply_optionArrT DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr) unit.
#[global] Instance Eq1_DSLPExc : Eq1 DSLPExc :=
  @Eq1_Arrow (optionArrT DSLPArr) (@ArrowEq_optionArrT DSLPArr ArrowEq_DSLPArr) unit.

Definition DSPExc (A : Type) : Type := optDSP unit A.
#[global] Instance Monad_DSPExc : Monad DSPExc :=
  @Monad_Arrow optDSP Arrow_optDSP ArrowApply_optDSP unit.
#[global] Instance Eq1_DSPExc : Eq1 DSPExc := @Eq1_Arrow optDSP ArrowEq_optDSP unit.
Definition MonadLawsE_DSPExc : @MonadLawsE DSPExc Eq1_DSPExc Monad_DSPExc :=
  @MonadLawsE_Arrow optDSP Arrow_optDSP ArrowApply_optDSP ArrowEq_optDSP
    ArrowLaws_optDSP ArrowApplyLaws_optDSP unit.

Definition ASLPExc (A : Type) : Type := optASLP unit A.
#[global] Instance Monad_ASLPExc : Monad ASLPExc :=
  @Monad_Arrow optASLP Arrow_optASLP ArrowApply_optASLP unit.
#[global] Instance Eq1_ASLPExc : Eq1 ASLPExc := @Eq1_Arrow optASLP ArrowEq_optASLP unit.

(* ================================================================= *)
(** ** The collapse maps, at [option A], are monad morphisms          *)
(* ================================================================= *)

Theorem dspExc_to_aspExc_morphism :
  @MonadMorphism DSPExc ASPExc Monad_DSPExc Monad_ASPExc Eq1_DSPExc Eq1_ASPExc
    (fun A => @dsp_to_asp (option A)).
Proof.
  exact (@MonadMorphism_optionArrT_rel DSPArr _ _ _ _ _ _ _ _
           ASPArr _ _ _ _ _ _ _ _ unit (fun A => @dsp_to_asp (option A))
           (fun A d x o => dsp_to_asp_rel d x o)).
Qed.

Theorem aspExc_to_dspExc_morphism :
  @MonadMorphism ASPExc DSPExc Monad_ASPExc Monad_DSPExc Eq1_ASPExc Eq1_DSPExc
    (fun A => @asp_to_dsp (option A)).
Proof.
  exact (@MonadMorphism_optionArrT_rel ASPArr _ _ _ _ _ _ _ _
           DSPArr _ _ _ _ _ _ _ _ unit (fun A => @asp_to_dsp (option A))
           (fun A m x o => asp_to_dsp_rel m x o)).
Qed.

Theorem aslpExc_to_dslpExc_morphism :
  @MonadMorphism ASLPExc DSLPExc Monad_ASLPExc Monad_DSLPExc Eq1_ASLPExc Eq1_DSLPExc
    (fun A => @aslp_to_dslp (option A)).
Proof.
  exact (@MonadMorphism_optionArrT_rel ASLPArr _ _ _ _ _ _ _ _
           DSLPArr _ _ _ _ _ _ _ _ unit (fun A => @aslp_to_dslp (option A))
           (fun A l x o => aslp_to_dslp_rel l x o)).
Qed.

Theorem dslpExc_to_aslpExc_morphism :
  @MonadMorphism DSLPExc ASLPExc Monad_DSLPExc Monad_ASLPExc Eq1_DSLPExc Eq1_ASLPExc
    (fun A => @dslp_to_aslp (option A)).
Proof.
  exact (@MonadMorphism_optionArrT_rel DSLPArr _ _ _ _ _ _ _ _
           ASLPArr _ _ _ _ _ _ _ _ unit (fun A => @dslp_to_aslp (option A))
           (fun A n x o => dslp_to_aslp_rel n x o)).
Qed.

(* ================================================================= *)
(** ** The orders                                                     *)
(* ================================================================= *)

Theorem OrderedMonad_ASPExc : @OrderedMonad ASPExc Monad_ASPExc Eq1_ASPExc (fun A => @ordASP (option A)).
Proof.
  constructor.
  - intro A. exact ordASP_PreOrder.
  - intros A m1 m2 H P o. exact (proj1 (H P o)).
  - intros A B m1 m2 Hm k1 k2 Hk.
    pose proof (proj1 (aspRel_incl m1 m2) Hm) as Hm'.
    refine (proj2 (@aspRel_incl unit (option B) (bind m1 k1) (bind m2 k2)) _). intros x o.
    cbn [bind Monad_ASPExc Monad_Arrow].
    rewrite !(@relO_bind ASPArr Arrow_ASPArr ArrowApply_ASPArr RelArrow_ASPArr
                RelArrowApply_ASPArr ArrowChoice_ASPArr RelArrowChoice_ASPArr).
    intros [o1 [H1 H2]]. exists o1. split; [ exact (Hm' x o1 H1) |].
    destruct o1 as [a|]; [ exact (proj1 (aspRel_incl (k1 a) (k2 a)) (Hk a) x o H2) | exact H2 ].
Qed.

Theorem OrderedMonad_DSLPExc : @OrderedMonad DSLPExc Monad_DSLPExc Eq1_DSLPExc (fun A => @ordDSLP (option A)).
Proof.
  constructor.
  - intro A. exact ordDSLP_PreOrder.
  - intros A m1 m2 H P o. exact (proj1 (H P o)).
  - intros A B m1 m2 Hm k1 k2 Hk.
    pose proof (proj1 (dslpRel_incl m1 m2) Hm) as Hm'.
    refine (proj2 (@dslpRel_incl unit (option B) (bind m1 k1) (bind m2 k2)) _). intros x o.
    cbn [bind Monad_DSLPExc Monad_Arrow].
    rewrite !(@relO_bind DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr RelArrow_DSLPArr
                RelArrowApply_DSLPArr ArrowChoice_DSLPArr RelArrowChoice_DSLPArr).
    intros [o1 [H1 H2]]. exists o1. split; [ exact (Hm' x o1 H1) |].
    destruct o1 as [a|]; [ exact (proj1 (dslpRel_incl (k1 a) (k2 a)) (Hk a) x o H2) | exact H2 ].
Qed.

Theorem OrderedMonad_DSPExc : @OrderedMonad DSPExc Monad_DSPExc Eq1_DSPExc (fun A => @ordDSP (option A)).
Proof.
  exact (@OrderedMonad_pullback _ _ _ _ _ _ (fun A => Eq1Equivalence_ASP (option A))
           (fun A => @dsp_to_asp (option A)) (fun A => @ordASP (option A))
           dspExc_to_aspExc_morphism OrderedMonad_ASPExc).
Qed.

Theorem OrderedMonad_ASLPExc : @OrderedMonad ASLPExc Monad_ASLPExc Eq1_ASLPExc (fun A => @ordASLP (option A)).
Proof.
  exact (@OrderedMonad_pullback _ _ _ _ _ _ (fun A => Eq1Equivalence_DSLP (option A))
           (fun A => @aslp_to_dslp (option A)) (fun A => @ordDSLP (option A))
           aslpExc_to_dslpExc_morphism OrderedMonad_DSLPExc).
Qed.
