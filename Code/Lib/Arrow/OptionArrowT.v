(** * Option arrow transformer (re-export).

    See [OptionArrowT/Core.v] for definitions and basic instances,
    [OptionArrowT/ArrowLaws.v] for generic arrow law proofs,
    [OptionArrowT/ArrowChoiceLaws.v] for generic ArrowChoiceLaws proof,
    [OptionArrowT/ArrowApplyLaws.v] for generic ArrowApplyLaws proof.

    Concrete instances for [optionArrT Rel] live in [Relational/Rel.v]. *)

From Incorrectness.Lib.Arrow.OptionArrowT Require Export Core ArrowLaws ArrowChoiceLaws ArrowApplyLaws.
