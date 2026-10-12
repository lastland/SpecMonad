# OptionArrowT context

Parent: [Classes](../CONTEXT.md). Public re-export: [OptionArrowT.v](../OptionArrowT.v).

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

[TransformerLaws.v](TransformerLaws.v) proves core and choice lift preservation
from base core/choice laws, and application preservation additionally from
base application laws. Composition/application reuse `optionArrT_comp_pure_l`;
dynamic application also reuses `app_postcompose_pure`. These lift contracts
are separate from the transformed-arrow law packages and morphism transport.

Application-law construction now imports `TransformerLaws` (which depends
only on Core/ArrowLaws) to obtain pure congruence via `lift_pure_congr`.
Constant-second reasoning uses the transformed core laws' shared
`second_constant`; choice reassociation uses shared `left_assoc_inverse` and
`left_context_iso`. Private copies are removed. `option_arr_ext` and
`option_app_law` remain bootstrap facts: the full transformed application
dictionary is not yet available. The pure-composition normalizations and
`core_opt_left` concern arbitrary option arrows and their carrier routing,
not just the image of lift; they establish transformed core/choice laws.

Read Core → relevant law module → [concrete tests](../../Taxonomy/Arrows/Tests/CONTEXT.md).
For state over option, continue to [StateArrowT](../StateArrowT/CONTEXT.md).
