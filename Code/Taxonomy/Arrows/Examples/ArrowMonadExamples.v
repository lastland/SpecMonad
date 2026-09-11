(** * Law resolution for the exact arrow-derived monad.

    A non-unit input checks the reader-like use of [arr I].  These goals
    name [Monad_Arrow] explicitly, so a bespoke monad instance on the
    same carrier cannot satisfy the check accidentally. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import
  PredArr RelPrePostArr RelSPPairArr SPostArr.

(** Pointwise arrow equalities, rather than Leibniz equality. *)
Definition pred_monad_laws :
  @MonadLawsE (PredArr bool)
    (@Eq1_Arrow _ ArrowEq_Pred bool)
    (@Monad_Arrow _ Arrow_Pred ArrowApply_Pred bool) := _.

Definition relprepost_monad_laws :
  @MonadLawsE (RelPrePostArr bool)
    (@Eq1_Arrow _ ArrowEq_RelPrePost bool)
    (@Monad_Arrow _ Arrow_RelPrePost ArrowApply_RelPrePost bool) := _.

(** Property-only angelic arrows: base, option, state, and state-over-option. *)
Definition property_asp_monad_laws :
  @MonadLawsE (SPostArr.PureASPostArr bool)
    (@Eq1_Arrow _ SPostArr.ArrowEq_PureASPostArr bool)
    (@Monad_Arrow _ SPostArr.Arrow_PureASPostArr
      SPostArr.ArrowApply_PureASPostArr bool) := _.

Definition property_option_asp_monad_laws :
  @MonadLawsE (SPostArr.optionASPArr bool)
    (@Eq1_Arrow _ SPostArr.ArrowEq_optionASPArr bool)
    (@Monad_Arrow _ SPostArr.Arrow_optionASPArr
      SPostArr.ArrowApply_optionASPArr bool) := _.

Definition property_state_asp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S SPostArr.PureASPostArr bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S _ SPostArr.ArrowEq_PureASPostArr) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _ SPostArr.Arrow_PureASPostArr)
      (@ArrowApply_stateArrT S _ SPostArr.Arrow_PureASPostArr
        SPostArr.ArrowApply_PureASPostArr) bool) := _.

Definition property_state_option_asp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S SPostArr.optionASPArr bool)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptASP S) bool)
    (@Monad_Arrow _ (SPostArr.Arrow_stateOptASP S)
      (SPostArr.ArrowApply_stateOptASP S) bool) := _.

(** Coupled demonic-liberal arrows exercise the other SP presentation. *)
Definition coupled_dslp_monad_laws :
  @MonadLawsE (RelSPPairArr.PureDSLPostArr bool)
    (@Eq1_Arrow _ RelSPPairArr.ArrowEq_PureDSLPostArr bool)
    (@Monad_Arrow _ RelSPPairArr.Arrow_PureDSLPostArr
      RelSPPairArr.ArrowApply_PureDSLPostArr bool) := _.

Definition coupled_option_dslp_monad_laws :
  @MonadLawsE (RelSPPairArr.optionDSLPArr bool)
    (@Eq1_Arrow _ (@ArrowEq_optionArrT _ RelSPPairArr.ArrowEq_PureDSLPostArr) bool)
    (@Monad_Arrow _ (@Arrow_optionArrT _ RelSPPairArr.Arrow_PureDSLPostArr
        RelSPPairArr.ArrowChoice_PureDSLPostArr)
      (@ArrowApply_optionArrT _ RelSPPairArr.Arrow_PureDSLPostArr
        RelSPPairArr.ArrowChoice_PureDSLPostArr
        RelSPPairArr.ArrowApply_PureDSLPostArr) bool) := _.

Definition coupled_state_dslp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S RelSPPairArr.PureDSLPostArr bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S _ RelSPPairArr.ArrowEq_PureDSLPostArr) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _ RelSPPairArr.Arrow_PureDSLPostArr)
      (@ArrowApply_stateArrT S _ RelSPPairArr.Arrow_PureDSLPostArr
        RelSPPairArr.ArrowApply_PureDSLPostArr) bool) := _.

Definition coupled_state_option_dslp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S RelSPPairArr.optionDSLPArr bool)
    (@Eq1_Arrow _ (RelSPPairArr.ArrowEq_stateOptDSLP S) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _
      (@Arrow_optionArrT _ RelSPPairArr.Arrow_PureDSLPostArr
        RelSPPairArr.ArrowChoice_PureDSLPostArr))
      (RelSPPairArr.ArrowApply_stateOptDSLP S) bool) := _.
