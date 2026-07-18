(** * Option arrow transformer (re-export).

    See [OptionArrowT/Core.v] for definitions and basic instances,
    [OptionArrowT/ArrowLaws.v] for generic arrow law proofs,
    [OptionArrowT/ArrowChoiceLaws.v] for generic ArrowChoiceLaws proof,
    [OptionArrowT/ArrowApplyLaws.v] for generic ArrowApplyLaws proof.

    The [optionArrT Rel] specialization and its law witnesses live in
    [Taxonomy/Rel.v] and [Taxonomy/RelFacts.v]. *)

From Incorrectness.Classes.OptionArrowT Require Export Core ArrowLaws ArrowChoiceLaws ArrowApplyLaws.
