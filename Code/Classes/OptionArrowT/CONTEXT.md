# OptionArrowT

Parent: [Classes context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Purpose and carrier

[Core.v](Core.v) defines `optionArrT arr A B := arr A (option B)`.
The transformer adds failure-propagating composition using base `ArrowChoice`.
[OptionArrowT.v](../OptionArrowT.v) is the public re-export of all four modules.

## Established vocabulary and operations

- `Arrow_optionArrT` lifts pure results through `Some`. Composition routes
  the first result through `to_sum`, base `arr_left`, and `collapse`:
  `Some b` reaches the next arrow; `None` bypasses it and remains `None`.
- `sequence_option` implements the result rearrangement for `arr_first`.
  A failed result discards the companion value rather than returning a pair.
- `ArrowChoice_optionArrT` uses `opt_rearrange`; an untouched right branch
  becomes `Some (inr c)`, while a failed left branch remains `None`.
- `ArrowEq_optionArrT` reuses base `arrow_eq` at output type `option B`.
- `ArrowT_optionArrT` lifts a base arrow by postcomposing with `Some`.
  This lift needs only `Arrow`; transformed composition needs `ArrowChoice`.
- `ArrowApply_optionArrT` uses base `arr_app` with result type `option B`.
  It requires base application as well as the choice needed for the
  transformed arrow instance.

## Law contracts and dependencies

- [ArrowLaws.v](ArrowLaws.v) proves `ArrowLaws_optionArrT` from base
  `ArrowLaws` and `ArrowChoiceLaws`, with their operations and equality.
- [ArrowChoiceLaws.v](ArrowChoiceLaws.v) proves `ArrowChoiceLaws_optionArrT`
  under the same base contracts; it requires no application instance.
- [ArrowApplyLaws.v](ArrowApplyLaws.v) additionally requires base
  `ArrowApply` and `ArrowApplyLaws`. It proves `ArrowApplyLaws_optionArrT`
  for main's single application law, `app_law`.

These modules import [Arrow.v](../Arrow.v), Coq libraries, and, in Core and
ArrowLaws, CoqHammer. Follow the explicit `@` base-instance applications in
the proofs rather than asking typeclass search to rediscover the base laws.

## Reading and boundaries

Read Core before the law files. Concrete `optionPred` and its base relation
belong to [PredArr.v](../../Taxonomy/Arrows/PredArr.v), not this directory.
`None` denotes failure structurally; its exception or divergence interpretation
belongs to the concrete model. No generic loop instance is defined here.

For state over option, continue to [StateArrowT](../StateArrowT/CONTEXT.md).
All four modules and the public re-export appear in
[_CoqProject](../../_CoqProject).
