# OptionArrowT

Parent: [Classes context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Purpose and operations

[Core.v](Core.v) defines `optionArrT arr A B := arr A (option B)`.
It adds failure-propagating composition to an arrow with `ArrowChoice`.
The public import [OptionArrowT.v](../OptionArrowT.v) re-exports all four modules.

- `Arrow_optionArrT` sends pure results through `Some`. Composition uses
  `to_sum`, base `arr_left`, and `collapse`: `Some` reaches the continuation,
  while `None` bypasses it.
- `sequence_option` moves an optional result through pairing; a failed
  result discards the companion value. `opt_rearrange` implements choice,
  preserving an untouched right branch as `Some (inr c)`.
- `ArrowEq_optionArrT` reuses base equality at output type `option B`.
- `ArrowT_optionArrT` lifts a base arrow by postcomposing with `Some`.
  This lift only needs `Arrow`; the transformed composition needs choice.
- `ArrowApply_optionArrT` uses base application at result type `option B`.
  `None` is a structural failure result here; concrete models determine
  whether an option layer represents an exception or divergence.

## Laws and dependencies

[ArrowLaws.v](ArrowLaws.v) derives `ArrowLaws_optionArrT` from base arrow and
choice laws. Its `optionArrT_comp_pure_l` reduces transformed pure
precomposition to base precomposition.
[ArrowChoiceLaws.v](ArrowChoiceLaws.v) lifts the choice contract.
[ArrowApplyLaws.v](ArrowApplyLaws.v) additionally requires base application
laws and lifts the full `ArrowApplyLaws` contract, using
[ArrowApplyFacts.v](../ArrowApplyFacts.v).

These are generic algebraic proofs. Concrete law-resolution checks belong to
[Taxonomy tests](../../Taxonomy/Arrows/Tests/CONTEXT.md), particularly
[ArrowTransformerInstances.v](../../Taxonomy/Arrows/Tests/ArrowTransformerInstances.v).
The [Classes regression](../Tests/CONTEXT.md) instead tests the generic
arrow-derived monad contract.

## Reading and composition

Read `Core.v`, then `ArrowLaws.v`, followed by the relevant extension laws.
All four modules and the re-export are in [_CoqProject](../../_CoqProject).
For state-over-option stacks, see [StateArrowT](../StateArrowT/CONTEXT.md).
For preservation maps through this layer, see
[ArrowMorphism.v](../ArrowMorphism.v).
