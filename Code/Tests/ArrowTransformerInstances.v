(** * Concrete option/state transformer instantiation checks.

    Plain definitions test generic law resolution without registering
    helper instances.  Explicit generic applications additionally check
    monad-transformer specialization and double-option application. *)

From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow ArrowMonad.
From Incorrectness.Lib.Arrow Require Import OptionArrowT StateArrowT.
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
