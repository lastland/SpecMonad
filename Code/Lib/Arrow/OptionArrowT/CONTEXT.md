# OptionArrowT context

Parent: [Lib](../../../CONTEXT.md). Public re-export: [OptionArrowT.v](../OptionArrowT.v).

[Core.v](Core.v) defines `optionArrT arr A B := arr A (option B)`.
Pure injects `Some`; composition uses `to_sum`, base left, and `collapse`:
`Some b` continues and `None` propagates. First uses `sequence_option`;
left uses `opt_rearrange`, leaving an untouched right branch successful.
Equality is base equality at output `option B`. Lift postcomposes a base
arrow with `Some`. Application uses base application at result `option B`.

The Arrow/choice operations require base choice; application also requires
base application. [ArrowLaws.v](ArrowLaws.v) and
[ArrowChoiceLaws.v](ArrowChoiceLaws.v) use base arrow/choice laws.
[ArrowApplyLaws.v](ArrowApplyLaws.v) proves the complete five-field contract,
including dynamic precomposition, from base arrow/choice/application laws.
These proofs inspect no concrete carrier; use explicit base dictionaries.
The law proofs reuse core pure-map fusion. Fixed-companion and constant
application steps reuse shared helpers with base-derived congruence and
application equations while constructing the transformed application laws.
There is no generic loop lift. `None`'s exception/divergence interpretation
belongs to a computation or observation, not this transformer.

Read Core → relevant law module → [concrete tests](../../../Tests/CONTEXT.md#concrete-arrow-instance-checks).
For state over option, continue to [StateArrowT](../StateArrowT/CONTEXT.md).
