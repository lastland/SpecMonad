(** * Concrete option/state transformer instantiation checks.

    Plain definitions test generic law resolution without registering
    helper instances.  Explicit generic applications additionally check
    monad-transformer specialization and double-option application. *)

From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow ArrowMonad.
From Incorrectness.Lib.Arrow Require Import OptionArrowT StateArrowT.
From Incorrectness.Lib.Arrow Require Import ArrowMorphism.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.Relational Require Import Rel.
From Incorrectness.SP Require Import SPostArr.

(** Pointwise transformer equivalence is the public equality, including
    for arrows selected at runtime and pointwise-related continuations. *)
Module PropertyEquality.

  Definition asp_core : ArrowLaws PureASPostArr := _.
  Definition asp_choice : ArrowChoiceLaws PureASPostArr := _.
  Definition asp_apply : ArrowApplyLaws PureASPostArr := _.
  Definition dslp_core : ArrowLaws PureDSLPostArr := _.
  Definition dslp_choice : ArrowChoiceLaws PureDSLPostArr := _.
  Definition dslp_apply : ArrowApplyLaws PureDSLPostArr := _.

  Example asp_pointwise {A B} (f g : PureASPostArr A B) :
    arrow_eq f g <-> (forall P b, getASP f P b <-> getASP g P b).
  Proof. reflexivity. Qed.

  Example dslp_pointwise {A B} (f g : PureDSLPostArr A B) :
    arrow_eq f g <-> (forall P b, getDSLP f P b <-> getDSLP g P b).
  Proof. reflexivity. Qed.

  Example asp_dynamic_application {X A B}
    (u v : X -> PureASPostArr A B * A)
    (H : forall x, (forall P b,
      getASP (fst (u x)) P b <-> getASP (fst (v x)) P b) /\
      snd (u x) = snd (v x)) :
    arrow_eq (compASP (arrASP u) appASP) (compASP (arrASP v) appASP).
  Proof.
    exact (@app_ext PureASPostArr _ _ ArrowEq_PureASPostArr _ X A B u v H).
  Qed.

  Example dslp_dynamic_application {X A B}
    (u v : X -> PureDSLPostArr A B * A)
    (H : forall x, (forall P b,
      getDSLP (fst (u x)) P b <-> getDSLP (fst (v x)) P b) /\
      snd (u x) = snd (v x)) :
    arrow_eq (compDSLP (arrDSLP u) appDSLP) (compDSLP (arrDSLP v) appDSLP).
  Proof.
    exact (@app_ext PureDSLPostArr _ _ ArrowEq_PureDSLPostArr _ X A B u v H).
  Qed.

  Example asp_continuation_congruence {I A B}
    (m n : PureASPostArr I A) (k l : A -> PureASPostArr I B)
    (Hmn : forall P a, getASP m P a <-> getASP n P a)
    (Hkl : forall a P b, getASP (k a) P b <-> getASP (l a) P b) :
    arrow_eq (bind_arrow PureASPostArr I m k) (bind_arrow PureASPostArr I n l).
  Proof.
    exact (@Proper_bind _ (Eq1_Arrow ArrowEq_PureASPostArr I)
      (Monad_Arrow PureASPostArr I) _ A B m n Hmn k l Hkl).
  Qed.

  Example dslp_continuation_congruence {I A B}
    (m n : PureDSLPostArr I A) (k l : A -> PureDSLPostArr I B)
    (Hmn : forall P a, getDSLP m P a <-> getDSLP n P a)
    (Hkl : forall a P b, getDSLP (k a) P b <-> getDSLP (l a) P b) :
    arrow_eq (bind_arrow PureDSLPostArr I m k) (bind_arrow PureDSLPostArr I n l).
  Proof.
    exact (@Proper_bind _ (Eq1_Arrow ArrowEq_PureDSLPostArr I)
      (Monad_Arrow PureDSLPostArr I) _ A B m n Hmn k l Hkl).
  Qed.

End PropertyEquality.

(* ================================================================= *)
(** ** [optionRel]: generic option-transformer laws, specialized      *)
(* ================================================================= *)

(** Because [Rel] already has [ArrowLaws], [ArrowChoiceLaws], and
    [ArrowApplyLaws] instances, [optionRel = optionArrT Rel]
    inherits the transformer laws from [Lib/Arrow/OptionArrowT] without
    any custom proof. *)

Definition ArrowLaws_optionRel : ArrowLaws optionRel := _.
Definition ArrowChoiceLaws_optionRel : ArrowChoiceLaws optionRel := _.
Definition ArrowApplyLaws_optionRel : ArrowApplyLaws optionRel := _.

(* ================================================================= *)
(** ** Monad-view spec types: laws through the monad transformers      *)
(* ================================================================= *)

(** Confirm [MonadLawsE] resolves through the transformer stack down
    to the arrow-derived [Monad (Rel unit)]. *)

Definition MonadLawsE__progRelM (S : Type)
  : @MonadLawsE (progRelM S) _ _ :=
  MonadLawsE_stateT S (optionT (Rel unit)).

Definition MonadLawsE__nditRelM (S : Type)
  : @MonadLawsE (nditRelM S) _ _ :=
  MonadLawsE_stateT S (optionT (optionT (Rel unit))).

(* ================================================================= *)
(** ** Relational stack coverage: option and state-over-option        *)
(* ================================================================= *)

(** The option and state-over-option stacks for both relational SP readings
    use [optionRel] and [stateArrT S optionRel]. Resolution composes
    the generic transformer laws over the base [Rel] instances. *)

Module RelOption.

  Definition ArrowEq_option : ArrowEq optionRel := _.

  Section StateOption.

    Variable S : Type.

    Definition ArrowEq_state
      : ArrowEq (stateArrT S optionRel) := _.
    Definition ArrowLaws_state
      : ArrowLaws (stateArrT S optionRel) := _.
    Definition ArrowChoice_state
      : ArrowChoice (stateArrT S optionRel) := _.
    Definition ArrowApply_state
      : ArrowApply (stateArrT S optionRel) := _.
    Definition ArrowChoiceLaws_state
      : ArrowChoiceLaws (stateArrT S optionRel) := _.
    Definition ArrowApplyLaws_state
      : ArrowApplyLaws (stateArrT S optionRel) := _.

  End StateOption.

End RelOption.

(* ================================================================= *)
(** ** Double-option application laws                                  *)
(* ================================================================= *)

(** A second option layer also supports higher-order application and
    its static law.  These witnesses exercise the generic dictionaries
    of the property-only presentation. *)
Example nested_optionASP_apply_law {A B}
  (f : optionArrT SPostArr.optionASPArr A B) :
  @arr_comp (optionArrT SPostArr.optionASPArr)
    (@Arrow_optionArrT SPostArr.optionASPArr
      SPostArr.Arrow_optionASPArr SPostArr.ArrowChoice_optionASPArr)
    _ _ _
    (@arr_pure (optionArrT SPostArr.optionASPArr)
      (@Arrow_optionArrT SPostArr.optionASPArr
        SPostArr.Arrow_optionASPArr SPostArr.ArrowChoice_optionASPArr)
      _ _ (fun a => (f, a)))
    (@arr_app (optionArrT SPostArr.optionASPArr) _
      (@ArrowApply_optionArrT SPostArr.optionASPArr
        SPostArr.Arrow_optionASPArr SPostArr.ArrowChoice_optionASPArr
         SPostArr.ArrowApply_optionASPArr) _ _) = f.
Proof.
  apply SPostArr.PureASPostArr_eq.
  exact (@app_law _ _ _ _
    (@ArrowApplyLaws_optionArrT SPostArr.optionASPArr
      SPostArr.Arrow_optionASPArr SPostArr.ArrowChoice_optionASPArr
      SPostArr.ArrowApply_optionASPArr SPostArr.ArrowEq_optionASPArr
      SPostArr.ArrowLaws_optionASPArr SPostArr.ArrowChoiceLaws_optionASPArr
      SPostArr.ArrowApplyLaws_optionASPArr)
    A B f).
Qed.

(** Selected dictionaries are explicit even in nested resolution checks. *)
Module LiftLaws.
  Definition option_core : ArrowTLaw optionArrT ArrowT_optionArrT Rel
    Arrow_Rel ArrowEq_Rel (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowEq_optionArrT Rel ArrowEq_Rel) := _.
  Definition option_choice : ArrowChoiceTLaw optionArrT ArrowT_optionArrT Rel
    Arrow_Rel ArrowChoice_Rel ArrowEq_Rel (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowChoice_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowEq_optionArrT Rel ArrowEq_Rel) := _.
  Definition option_apply : ArrowApplyTLaw optionArrT ArrowT_optionArrT Rel
    Arrow_Rel ArrowApply_Rel ArrowEq_Rel (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel)
    (@ArrowEq_optionArrT Rel ArrowEq_Rel) := _.

  Definition OA := @Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel.
  Definition OC := @ArrowChoice_optionArrT Rel Arrow_Rel ArrowChoice_Rel.
  Definition OX := @ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel.
  Definition OE := @ArrowEq_optionArrT Rel ArrowEq_Rel.

  Definition double_option_core : ArrowTLaw optionArrT ArrowT_optionArrT
    optionRel OA OE (@Arrow_optionArrT optionRel OA OC)
    (@ArrowEq_optionArrT optionRel OE) := _.
  Definition double_option_choice : ArrowChoiceTLaw optionArrT ArrowT_optionArrT
    optionRel OA OC OE (@Arrow_optionArrT optionRel OA OC)
    (@ArrowChoice_optionArrT optionRel OA OC) (@ArrowEq_optionArrT optionRel OE) := _.
  Definition double_option_apply : ArrowApplyTLaw optionArrT ArrowT_optionArrT
    optionRel OA OX OE (@Arrow_optionArrT optionRel OA OC)
    (@ArrowApply_optionArrT optionRel OA OC OX) (@ArrowEq_optionArrT optionRel OE) := _.

  Section StateOption.
    Variable S : Type.
    Definition state_option_core : ArrowTLaw (stateArrT S) (ArrowT_stateArrT S)
      optionRel OA OE (@Arrow_stateArrT S optionRel OA)
      (@ArrowEq_stateArrT S optionRel OE) := _.
    Definition state_option_choice : ArrowChoiceTLaw (stateArrT S) (ArrowT_stateArrT S)
      optionRel OA OC OE (@Arrow_stateArrT S optionRel OA)
      (@ArrowChoice_stateArrT S optionRel OA OC) (@ArrowEq_stateArrT S optionRel OE) := _.
    Definition state_option_apply : ArrowApplyTLaw (stateArrT S) (ArrowT_stateArrT S)
      optionRel OA OX OE (@Arrow_stateArrT S optionRel OA)
      (@ArrowApply_stateArrT S optionRel OA OX) (@ArrowEq_stateArrT S optionRel OE) := _.

    Definition state_option_morphism : ArrowMorphism OA OC OX OE
      (@Arrow_stateArrT S optionRel OA) (@ArrowChoice_stateArrT S optionRel OA OC)
      (@ArrowApply_stateArrT S optionRel OA OX) (@ArrowEq_stateArrT S optionRel OE)
      (@arrowT_lift (stateArrT S) (ArrowT_stateArrT S) optionRel OA) :=
      arrowT_lift_morphism _ _ _ _ _ _ _ _ _ _ _
        state_option_core state_option_choice state_option_apply.

    Example state_option_lift_rewrite {A B C} (f g : optionRel A B)
      (h : optionRel B C) (H : forall a ob, f a ob <-> g a ob) :
      @arrow_eq (stateArrT S optionRel) (@ArrowEq_stateArrT S optionRel OE) A C
        (@arrowT_lift (stateArrT S) (ArrowT_stateArrT S) optionRel OA A C
          (@arr_comp optionRel OA A B C f h))
        (@arr_comp (stateArrT S optionRel) (@Arrow_stateArrT S optionRel OA) A B C
          (@arrowT_lift (stateArrT S) (ArrowT_stateArrT S) optionRel OA A B g)
          (@arrowT_lift (stateArrT S) (ArrowT_stateArrT S) optionRel OA B C h)).
    Proof.
      rewrite (@lift_comp _ _ _ _ _ _ _ state_option_core A B C f h).
      apply (@comp_proper _ _ _
        (@ArrowLaws_stateArrT S optionRel OA OE
          (@ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
            ArrowLaws_Rel ArrowChoiceLaws_Rel))).
      - exact (@lift_proper _ _ _ _ _ _ _ state_option_core A B f g H).
      - reflexivity.
    Qed.
  End StateOption.

  Definition asp_option_core : ArrowTLaw optionArrT ArrowT_optionArrT PureASPostArr
    Arrow_PureASPostArr ArrowEq_PureASPostArr
    (@Arrow_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr)
    (@ArrowEq_optionArrT PureASPostArr ArrowEq_PureASPostArr) := _.
  Definition dslp_option_core : ArrowTLaw optionArrT ArrowT_optionArrT PureDSLPostArr
    Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr
    (@Arrow_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr)
    (@ArrowEq_optionArrT PureDSLPostArr ArrowEq_PureDSLPostArr) := _.

  (** No reflection to ordinary equality: use the semantic hypothesis directly. *)
  Example asp_lift_proper {A B} (f g : PureASPostArr A B)
    (H : forall P b, getASP f P b <-> getASP g P b) :
    @arrow_eq (optionArrT PureASPostArr)
      (@ArrowEq_optionArrT PureASPostArr ArrowEq_PureASPostArr) A B
      (@arrowT_lift optionArrT ArrowT_optionArrT PureASPostArr Arrow_PureASPostArr A B f)
      (@arrowT_lift optionArrT ArrowT_optionArrT PureASPostArr Arrow_PureASPostArr A B g).
  Proof. exact (@lift_proper _ _ _ _ _ _ _ asp_option_core A B f g H). Qed.

  Example dslp_lift_comp_semantic {A B C} (f g : PureDSLPostArr A B)
    (h : PureDSLPostArr B C)
    (H : forall P b, getDSLP f P b <-> getDSLP g P b) :
    @arrow_eq (optionArrT PureDSLPostArr)
      (@ArrowEq_optionArrT PureDSLPostArr ArrowEq_PureDSLPostArr) A C
      (@arrowT_lift optionArrT ArrowT_optionArrT PureDSLPostArr Arrow_PureDSLPostArr A C
        (compDSLP f h))
      (@arr_comp (optionArrT PureDSLPostArr)
        (@Arrow_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr) A B C
        (@arrowT_lift optionArrT ArrowT_optionArrT PureDSLPostArr Arrow_PureDSLPostArr A B g)
        (@arrowT_lift optionArrT ArrowT_optionArrT PureDSLPostArr Arrow_PureDSLPostArr B C h)).
  Proof.
    transitivity (@arrowT_lift optionArrT ArrowT_optionArrT
      PureDSLPostArr Arrow_PureDSLPostArr A C (compDSLP g h)).
    - apply (@lift_proper _ _ _ _ _ _ _ dslp_option_core).
      apply (@comp_proper PureDSLPostArr Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr
        ArrowLaws_PureDSLPostArr); [exact H | reflexivity].
    - exact (@lift_comp _ _ _ _ _ _ _ dslp_option_core A B C g h).
  Qed.
End LiftLaws.

Example nested_optionDSLP_apply_law {A B}
  (f : optionArrT SPostArr.optionDSLPArr A B) :
  @arr_comp (optionArrT SPostArr.optionDSLPArr)
    (@Arrow_optionArrT SPostArr.optionDSLPArr
      SPostArr.Arrow_optionDSLPArr SPostArr.ArrowChoice_optionDSLPArr)
    _ _ _
    (@arr_pure (optionArrT SPostArr.optionDSLPArr)
      (@Arrow_optionArrT SPostArr.optionDSLPArr
        SPostArr.Arrow_optionDSLPArr SPostArr.ArrowChoice_optionDSLPArr)
      _ _ (fun a => (f, a)))
    (@arr_app (optionArrT SPostArr.optionDSLPArr) _
      (@ArrowApply_optionArrT SPostArr.optionDSLPArr
        SPostArr.Arrow_optionDSLPArr SPostArr.ArrowChoice_optionDSLPArr
         SPostArr.ArrowApply_optionDSLPArr) _ _) = f.
Proof.
  apply SPostArr.PureDSLPostArr_eq.
  exact (@app_law _ _ _ _
    (@ArrowApplyLaws_optionArrT SPostArr.optionDSLPArr
      SPostArr.Arrow_optionDSLPArr SPostArr.ArrowChoice_optionDSLPArr
      SPostArr.ArrowApply_optionDSLPArr SPostArr.ArrowEq_optionDSLPArr
      SPostArr.ArrowLaws_optionDSLPArr SPostArr.ArrowChoiceLaws_optionDSLPArr
      SPostArr.ArrowApplyLaws_optionDSLPArr)
    A B f).
Qed.
