(** * Concrete option/state transformer instantiation checks.

    Plain definitions test generic law resolution without registering
    helper instances.  Explicit generic applications additionally check
    monad-transformer specialization and double-option application. *)

From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad.
From Incorrectness.Classes Require Import OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPPairArr SPostArr.

(* ================================================================= *)
(** ** [optionRel]: generic option-transformer laws, specialized      *)
(* ================================================================= *)

(** Because [Rel] already has [ArrowLaws], [ArrowChoiceLaws], and
    [ArrowApplyLaws] instances, [optionRel = optionArrT Rel]
    inherits the transformer laws from [Classes/OptionArrowT] without
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
(** ** Coupled presentations: option-level dictionaries                *)
(* ================================================================= *)

(** These used to be registered (as local/global instances whose bodies
    were [:= _]) in [RelSPPairArr.v].  They are plain definitions here:
    resolution must compose [Arrow*_optionArrT] over the coupled base
    laws, with no registered per-stack dictionary. *)

Module CoupledASP.

  Definition ArrowEq_option : ArrowEq RelSPPairArr.optionASPArr := _.
  Definition ArrowLaws_option : ArrowLaws RelSPPairArr.optionASPArr := _.
  Definition ArrowChoiceLaws_option
    : ArrowChoiceLaws RelSPPairArr.optionASPArr := _.
  Definition ArrowApplyLaws_option
    : ArrowApplyLaws RelSPPairArr.optionASPArr := _.

  Section StateOption.

    Variable S : Type.

    Definition ArrowEq_state
      : ArrowEq (stateArrT S RelSPPairArr.optionASPArr) := _.
    Definition ArrowLaws_state
      : ArrowLaws (stateArrT S RelSPPairArr.optionASPArr) := _.
    Definition ArrowChoice_state
      : ArrowChoice (stateArrT S RelSPPairArr.optionASPArr) := _.
    Definition ArrowApply_state
      : ArrowApply (stateArrT S RelSPPairArr.optionASPArr) := _.
    Definition ArrowChoiceLaws_state
      : ArrowChoiceLaws (stateArrT S RelSPPairArr.optionASPArr) := _.
    Definition ArrowApplyLaws_state
      : ArrowApplyLaws (stateArrT S RelSPPairArr.optionASPArr) := _.

  End StateOption.

End CoupledASP.

Module CoupledDSLP.

  Definition ArrowEq_option : ArrowEq RelSPPairArr.optionDSLPArr := _.
  Definition ArrowLaws_option : ArrowLaws RelSPPairArr.optionDSLPArr := _.
  Definition ArrowChoiceLaws_option
    : ArrowChoiceLaws RelSPPairArr.optionDSLPArr := _.
  Definition ArrowApplyLaws_option
    : ArrowApplyLaws RelSPPairArr.optionDSLPArr := _.

  Section StateOption.

    Variable S : Type.

    Definition ArrowEq_state
      : ArrowEq (stateArrT S RelSPPairArr.optionDSLPArr) := _.
    Definition ArrowLaws_state
      : ArrowLaws (stateArrT S RelSPPairArr.optionDSLPArr) := _.
    Definition ArrowChoice_state
      : ArrowChoice (stateArrT S RelSPPairArr.optionDSLPArr) := _.
    Definition ArrowApply_state
      : ArrowApply (stateArrT S RelSPPairArr.optionDSLPArr) := _.
    Definition ArrowChoiceLaws_state
      : ArrowChoiceLaws (stateArrT S RelSPPairArr.optionDSLPArr) := _.
    Definition ArrowApplyLaws_state
      : ArrowApplyLaws (stateArrT S RelSPPairArr.optionDSLPArr) := _.

  End StateOption.

End CoupledDSLP.

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
  exact (@app_law _ _ _ _
    (@ArrowApplyLaws_optionArrT SPostArr.optionDSLPArr
      SPostArr.Arrow_optionDSLPArr SPostArr.ArrowChoice_optionDSLPArr
      SPostArr.ArrowApply_optionDSLPArr SPostArr.ArrowEq_optionDSLPArr
      SPostArr.ArrowLaws_optionDSLPArr SPostArr.ArrowChoiceLaws_optionDSLPArr
      SPostArr.ArrowApplyLaws_optionDSLPArr)
    A B f).
Qed.
