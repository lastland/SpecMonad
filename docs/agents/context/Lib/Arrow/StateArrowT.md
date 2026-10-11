# StateArrowT context

Parent: [Lib](../../Code.md). Public re-export: [StateArrowT.v](../../../../../Code/Lib/Arrow/StateArrowT.v).

[Core.v](../../../../../Code/Lib/Arrow/StateArrowT/Core.v) defines `stateArrT S arr A B := arr (A * S) (B * S)`.
Pure preserves state; composition delegates to base composition. First moves
the companion apart from state using `state_shuffle_in/out`. Lift uses base
first. Choice moves state through sums with `sum_distribute/undistribute`.
Application rearranges `((f,a),s)` to `(f,(a,s))` before base application.
Equality is base equality at these paired types.

Core derives arrow laws from base arrow laws. Choice laws additionally use
base choice/laws. [ArrowApplyLaws.v](../../../../../Code/Lib/Arrow/StateArrowT/ArrowApplyLaws.v) lifts all five
application fields from the base contract without requiring choice.
Keep explicit dictionaries to avoid recursive option/state instance search.
Pure-map fusion and shuffle cancellation reuse core facts with explicit base
pure-function congruence.
No loop lifting is supplied.

Over option the carrier becomes `arr (A * S) (option (B * S))`: failure has
no final state. Transformer order matters. Read Core, law modules, then
[concrete tests](../../Tests.md#concrete-arrow-instance-checks). Generic proofs are
algebraic, not inspections of a concrete relation or SP carrier.
