(** * Pure congruence search from core laws alone.

    Deliberately omit application and lift-law modules for the transformers.
    Abstract lift-only resolution is checked in [ArrowMonadRegression.v]. *)
From Coq Require Import Morphisms.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.OptionArrowT Require Import Core ArrowLaws.
From Incorrectness.Classes.StateArrowT Require Import Core.

Section BaseResolution.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HE : ArrowEq arr} {HL : @ArrowLaws arr HA HE}.

  Definition base_pure_proper {A B} :
    Proper (pointwise_relation A (@eq B) ==> @arrow_eq arr HE A B)
      (@arr_pure arr HA A B) := _.

  Lemma base_pure_rewrite {A B} (f g : A -> B) (H : forall a, f a = g a) :
    @arrow_eq arr HE A B (@arr_pure arr HA A B f) (@arr_pure arr HA A B g).
  Proof. f_equiv. exact H. Qed.
End BaseResolution.

(** Search may use transformed core laws, but no application or lift laws. *)
Section TransformerCoreResolution.
  Context (S : Type) {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HE : ArrowEq arr}
    {HL : @ArrowLaws arr HA HE} {HCL : @ArrowChoiceLaws arr HA HC HE}.

  Definition option_pure_proper {A B} :
    Proper (pointwise_relation A (@eq B) ==>
      @arrow_eq (optionArrT arr) (@ArrowEq_optionArrT arr HE) A B)
      (@arr_pure (optionArrT arr) (@Arrow_optionArrT arr HA HC) A B) := _.

  Definition state_pure_proper {A B} :
    Proper (pointwise_relation A (@eq B) ==>
      @arrow_eq (stateArrT S arr) (@ArrowEq_stateArrT S arr HE) A B)
      (@arr_pure (stateArrT S arr) (@Arrow_stateArrT S arr HA) A B) := _.

  Definition state_option_pure_proper {A B} :
    Proper (pointwise_relation A (@eq B) ==>
      @arrow_eq (stateArrT S (optionArrT arr))
        (@ArrowEq_stateArrT S (optionArrT arr) (@ArrowEq_optionArrT arr HE)) A B)
      (@arr_pure (stateArrT S (optionArrT arr))
        (@Arrow_stateArrT S (optionArrT arr) (@Arrow_optionArrT arr HA HC)) A B) := _.

  Lemma option_pure_rewrite {A B} (f g : A -> B) (H : forall a, f a = g a) :
    @arrow_eq (optionArrT arr) (@ArrowEq_optionArrT arr HE) A B
      (@arr_pure _ (@Arrow_optionArrT arr HA HC) A B f)
      (@arr_pure _ (@Arrow_optionArrT arr HA HC) A B g).
  Proof. f_equiv. exact H. Qed.

  Lemma state_option_pure_rewrite {A B} (f g : A -> B) (H : forall a, f a = g a) :
    @arrow_eq (stateArrT S (optionArrT arr))
      (@ArrowEq_stateArrT S (optionArrT arr) (@ArrowEq_optionArrT arr HE)) A B
      (@arr_pure _ (@Arrow_stateArrT S (optionArrT arr) (@Arrow_optionArrT arr HA HC)) A B f)
      (@arr_pure _ (@Arrow_stateArrT S (optionArrT arr) (@Arrow_optionArrT arr HA HC)) A B g).
  Proof. apply state_option_pure_proper. exact H. Qed.
End TransformerCoreResolution.

(** Search must not manufacture a congruence premise. *)
Section MissingPremise.
  Context (T : (Type -> Type -> Type) -> Type -> Type -> Type) (HT : ArrowT T)
    (arr : Type -> Type -> Type) (SA : Arrow arr) (SE : ArrowEq arr)
    (DA : Arrow (T arr)) (DE : ArrowEq (T arr))
    (L : ArrowTLaw T HT arr SA SE DA DE).

  Fail Definition missing_source_pure_proper {A B} :
    Proper (pointwise_relation A (@eq B) ==> @arrow_eq arr SE A B)
      (@arr_pure arr SA A B) := _.

  Fail Definition missing_lifted_pure_proper {A B} :
    Proper (pointwise_relation A (@eq B) ==> @arrow_eq (T arr) DE A B)
      (@arr_pure (T arr) DA A B) := _.
End MissingPremise.
