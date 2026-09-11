(** * Law resolution for the exact arrow-derived monad.

    A non-unit input checks the reader-like use of [arr I].  These goals
    name [Monad_Arrow] explicitly, so a bespoke monad instance on the
    same carrier cannot satisfy the check accidentally. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import
  PredArr PrePostArr RelPrePostArr RelSPPairArr SPostArr SPostArrMonad.

(** The concrete bundle must reuse the generic dictionary itself. *)
Example coupled_asp_reuses_arrow (I : Type) :
  @RelSPPairArr.Monad_PureASPostArr I =
  @Monad_Arrow RelSPPairArr.PureASPostArr RelSPPairArr.Arrow_PureASPostArr
    RelSPPairArr.ArrowApply_PureASPostArr I.
Proof. reflexivity. Qed.

(** These monads are inferred without naming the concrete aliases.  The
    equalities check both automatic resolution and the public alias bodies. *)
Definition inferred_pred_monad : Monad (PredArr bool) := _.
Definition inferred_prepost_monad : Monad (PrePostArr bool) := _.
Definition inferred_relprepost_monad : Monad (RelPrePostArr bool) := _.
Definition inferred_asp_monad : Monad (RelSPPairArr.PureASPostArr bool) := _.
Definition inferred_dslp_monad : Monad (RelSPPairArr.PureDSLPostArr bool) := _.

Example pred_reuses_arrow :
  inferred_pred_monad = @Monad_Pred bool /\
  @Monad_Pred bool = @Monad_Arrow PredArr Arrow_Pred ArrowApply_Pred bool.
Proof. split; reflexivity. Qed.

Example prepost_reuses_arrow :
  inferred_prepost_monad = @Monad_PrePost bool /\
  @Monad_PrePost bool = @Monad_Arrow PrePostArr Arrow_PrePost ArrowApply_PrePost bool.
Proof. split; reflexivity. Qed.

Example relprepost_reuses_arrow :
  inferred_relprepost_monad = @Monad_RelPrePost bool /\
  @Monad_RelPrePost bool =
    @Monad_Arrow RelPrePostArr Arrow_RelPrePost ArrowApply_RelPrePost bool.
Proof. split; reflexivity. Qed.

Example asp_resolution_uses_arrow :
  inferred_asp_monad = @RelSPPairArr.Monad_PureASPostArr bool /\
  @RelSPPairArr.Monad_PureASPostArr bool =
    @Monad_Arrow RelSPPairArr.PureASPostArr RelSPPairArr.Arrow_PureASPostArr
      RelSPPairArr.ArrowApply_PureASPostArr bool.
Proof. split; reflexivity. Qed.

Example dslp_reuses_arrow :
  inferred_dslp_monad = @RelSPPairArr.Monad_PureDSLPostArr bool /\
  @RelSPPairArr.Monad_PureDSLPostArr bool =
    @Monad_Arrow RelSPPairArr.PureDSLPostArr RelSPPairArr.Arrow_PureDSLPostArr
      RelSPPairArr.ArrowApply_PureDSLPostArr bool.
Proof. split; reflexivity. Qed.

(** Canonical concrete equalities must resolve the generic law instances. *)
Definition pred_canonical_laws :
  @MonadLawsE (PredArr bool) (@Eq1_Pred bool) inferred_pred_monad := _.
Definition prepost_canonical_laws :
  @MonadLawsE (PrePostArr bool) (@Eq1_PrePost bool) inferred_prepost_monad := _.
Definition relprepost_canonical_laws :
  @MonadLawsE (RelPrePostArr bool) (@Eq1_RelPrePost bool)
    inferred_relprepost_monad := _.
Definition asp_canonical_laws :
  @MonadLawsE (RelSPPairArr.PureASPostArr bool)
    (@RelSPPairArr.Eq1_PureASPostArr bool) inferred_asp_monad := _.
Definition dslp_canonical_laws :
  @MonadLawsE (RelSPPairArr.PureDSLPostArr bool)
    (@RelSPPairArr.Eq1_PureDSLPostArr bool) inferred_dslp_monad := _.

Definition pred_canonical_equivalence :
  @Eq1Equivalence (PredArr bool) inferred_pred_monad (@Eq1_Pred bool) := _.
Definition prepost_canonical_equivalence :
  @Eq1Equivalence (PrePostArr bool) inferred_prepost_monad (@Eq1_PrePost bool) := _.
Definition relprepost_canonical_equivalence :
  @Eq1Equivalence (RelPrePostArr bool) inferred_relprepost_monad
    (@Eq1_RelPrePost bool) := _.
Definition asp_canonical_equivalence :
  @Eq1Equivalence (RelSPPairArr.PureASPostArr bool) inferred_asp_monad
    (@RelSPPairArr.Eq1_PureASPostArr bool) := _.
Definition dslp_canonical_equivalence :
  @Eq1Equivalence (RelSPPairArr.PureDSLPostArr bool) inferred_dslp_monad
    (@RelSPPairArr.Eq1_PureDSLPostArr bool) := _.

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

(** The named monad dictionaries of [SPostArrMonad] alias the same
    property-only stacks.  Typeclass resolution does not see through the
    aliases, so the generic law instance is named explicitly, at
    arbitrary state. *)
Definition spostarr_asp_monad_laws (S : Type) :
  @MonadLawsE (SPostArr.ASPostArr S)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptASP S) unit)
    (Monad_ASPostArr S) :=
  @MonadLawsE_Arrow (stateArrT S SPostArr.optionASPArr)
    (SPostArr.Arrow_stateOptASP S) (SPostArr.ArrowApply_stateOptASP S)
    (SPostArr.ArrowEq_stateOptASP S) (SPostArr.ArrowLaws_stateOptASP S)
    (SPostArr.ArrowApplyLaws_stateOptASP S) unit.

Definition spostarr_dslp_monad_laws (S : Type) :
  @MonadLawsE (SPostArr.DSLPostArr S)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptDSLP S) unit)
    (Monad_DSLPostArr S) :=
  @MonadLawsE_Arrow (stateArrT S SPostArr.optionDSLPArr)
    (SPostArr.Arrow_stateOptDSLP S) (SPostArr.ArrowApply_stateOptDSLP S)
    (SPostArr.ArrowEq_stateOptDSLP S) (SPostArr.ArrowLaws_stateOptDSLP S)
    (SPostArr.ArrowApplyLaws_stateOptDSLP S) unit.
