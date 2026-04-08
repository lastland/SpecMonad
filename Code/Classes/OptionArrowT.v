(** * Option arrow transformer (re-export).

    See [OptionArrowT/Core.v] for definitions and basic instances,
    [OptionArrowT/ArrowLaws.v] for generic arrow law proofs,
    [OptionArrowT/ArrowChoiceLaws.v] for generic ArrowChoiceLaws proof,
    [OptionArrowT/ArrowApplyLaws.v] for generic ArrowApplyLaws proof,
    [OptionArrowT/Pred.v] for concrete [optionPred] instances. *)

From Incorrectness.Classes.OptionArrowT Require Export Core ArrowLaws ArrowChoiceLaws ArrowApplyLaws Pred.
