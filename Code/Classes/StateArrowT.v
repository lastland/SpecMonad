(** * Generic state arrow transformer (re-export).

    See [StateArrowT/Core.v] for definitions and basic instances,
    [StateArrowT/ArrowChoiceLaws.v] for generic ArrowChoiceLaws proof,
    [StateArrowT/ArrowApplyLaws.v] for generic ArrowApplyLaws proof. *)

From Incorrectness.Classes.StateArrowT Require Export
  Core ArrowChoiceLaws ArrowApplyLaws.
