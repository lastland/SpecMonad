# StateArrowT

Parent: [Classes context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Purpose and carrier

[Core.v](Core.v) defines `stateArrT S arr A B := arr (A * S) (B * S)`.
The transformer threads state through an arrow's input and output.
[StateArrowT.v](../StateArrowT.v) re-exports Core and both extension-law files.

## Established vocabulary and operations

- `Arrow_stateArrT` needs only a base `Arrow`. Pure arrows preserve state;
  composition delegates directly to base `arr_comp`.
- `state_shuffle_in` maps `((a, c), s)` to `((a, s), c)` before base
  `arr_first`; `state_shuffle_out` restores the output pairing afterward.
  The companion `c` is separate from the state passed through the arrow.
- `ArrowT_stateArrT` lifts an arrow through base `arr_first`, carrying
  an unchanged state alongside its result.
- `ArrowEq_stateArrT` uses base `arrow_eq` at the paired input/output types.
- `ArrowChoice_stateArrT` needs base choice. `sum_distribute` and
  `sum_undistribute` move state into and out of the sum around base `arr_left`.
- `ArrowApply_stateArrT` rearranges `((f, a), s)` into `(f, (a, s))`
  before base `arr_app`. Application does not require base choice.

## Law contracts and dependencies

Unlike OptionArrowT, Core also proves `ArrowLaws_stateArrT`, using base
`ArrowLaws`. [ArrowChoiceLaws.v](ArrowChoiceLaws.v) proves
`ArrowChoiceLaws_stateArrT` from base arrow and choice laws.
[ArrowApplyLaws.v](ArrowApplyLaws.v) proves `ArrowApplyLaws_stateArrT`
from base arrow and application laws; main's application contract is `app_law`.
These proofs depend on base contracts and product/sum rearrangements, not
on a concrete relation. The modules import [Arrow.v](../Arrow.v) and Coq libraries.

The choice/application definitions and proofs explicitly select base instances.
Preserve those selections when editing nested transformer operations;
see the root guidance on recursive typeclass search.

## Composition and boundaries

With [OptionArrowT](../OptionArrowT/CONTEXT.md) underneath, the carrier is
`arr (A * S) (option (B * S))`: a failed output has no final state.
Transformer order therefore matters. Concrete stacks such as `progPredArr`
live in [PredArr.v](../../Taxonomy/Arrows/PredArr.v).
This directory defines no generic loop lifting or concrete specification carrier.

Start with Core's operations and shuffles, then read the required law package.
All three modules and the public re-export are listed in
[_CoqProject](../../_CoqProject).
