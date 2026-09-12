# StateArrowT

Parent: [Classes context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Purpose and operations

[Core.v](Core.v) defines `stateArrT S arr A B := arr (A * S) (B * S)`.
It threads state through both ends of an arrow. The public import
[StateArrowT.v](../StateArrowT.v) re-exports the three implementation modules.

- `Arrow_stateArrT` preserves state in pure arrows and uses base composition
  directly. `state_shuffle_in` and `state_shuffle_out` route state through
  `arr_first` while keeping the ordinary companion value separate.
- `ArrowT_stateArrT` lifts a base arrow using base `arr_first`.
- `ArrowEq_stateArrT` reuses base equality at the paired input/output types.
- `sum_distribute` and `sum_undistribute` route state through choice.
  `ArrowChoice_stateArrT` requires base choice and leaves the bypassed
  branch's state unchanged.
- `ArrowApply_stateArrT` rearranges `((f, a), s)` into `(f, (a, s))` and
  invokes base application. Its construction does not require choice.

## Laws and dependencies

Unlike the option transformer, `Core.v` also proves `ArrowLaws_stateArrT`.
[ArrowChoiceLaws.v](ArrowChoiceLaws.v) derives the choice laws from base
arrow/choice laws. [ArrowApplyLaws.v](ArrowApplyLaws.v) derives the full
application contract from base arrow/application laws.
The proofs are algebraic and independent of a concrete specification carrier.

With [OptionArrowT](../OptionArrowT/CONTEXT.md) underneath, the carrier is
`arr (A * S) (option (B * S))`: a failed output contains no final state.
Do not infer the opposite transformer order from the shared use of state
and option. [ArrowMorphism.v](../ArrowMorphism.v) lifts preservation maps,
and [RelArrowCoherence.v](../RelArrowCoherence.v) gives relational semantics
for state-over-option operations and arrow-derived bind.

## Reading and checks

Start with the operations and shuffles in `Core.v`, then its core laws;
read extension laws only for the required contract.
All three modules and the re-export are in [_CoqProject](../../_CoqProject).
[Concrete Taxonomy tests](../../Taxonomy/Arrows/Tests/CONTEXT.md) check stack
instances in [ArrowTransformerInstances.v](../../Taxonomy/Arrows/Tests/ArrowTransformerInstances.v).
[Generic Classes regressions](../Tests/CONTEXT.md) cover the arrow-derived
monad contract separately.
