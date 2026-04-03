(** * Option arrow transformer (re-export).

    See [OptionArrowT/Core.v] for definitions and basic instances,
    [OptionArrowT/ArrowLaws.v] for generic arrow law proofs,
    [OptionArrowT/ArrowChoiceLaws.v] for generic ArrowChoiceLaws proof,
    [OptionArrowT/ArrowApplyLaws.v] for generic ArrowApplyLaws proof,
    [OptionArrowT/SPArr.v] for concrete [optionSPArr] instances. *)

From Incorrectness.Classes.OptionArrowT Require Export Core ArrowLaws ArrowChoiceLaws ArrowApplyLaws SPArr.
