# StateArrowT context

Parent: [Classes](../CONTEXT.md). Public re-export: [StateArrowT.v](../StateArrowT.v).

[Core.v](Core.v) defines `stateArrT S arr A B := arr (A * S) (B * S)`.
Pure preserves state; composition delegates to base composition. First moves
the companion apart from state using `state_shuffle_in/out`. Lift uses base
first. Choice moves state through sums with `sum_distribute/undistribute`.
Application rearranges `((f,a),s)` to `(f,(a,s))` before base application.
Equality is base equality at these paired types.

Core derives arrow laws from base arrow laws. Choice laws additionally use
base choice/laws. [ArrowApplyLaws.v](ArrowApplyLaws.v) lifts all five
application fields from the base contract without requiring choice.
Keep explicit dictionaries to avoid recursive option/state instance search.
Pure-map fusion and shuffle cancellation reuse core facts with selected base
law dictionaries. The proof of the core `pure_proper` field maps pointwise
equality through the state-preserving pair using the base pure field, without
invoking functional extensionality. The complete opaque core-law dictionary,
including projections from it, retains the other fields' extensionality dependency.
No loop lifting is supplied.

[TransformerLaws.v](TransformerLaws.v) proves the three lift contracts.
Core lift preservation needs only base core laws; choice additionally needs
base choice laws. Application uses base application laws without choice,
reusing `arrow_ext`, `app_constant`, and `first_constant`.

The private `lift_first_state` wrapper is removed; its algebra establishes
the instance's `lift_first` field directly. Shuffle cancellation uses
`pure_comp_ext` at its sole call site. Application construction reuses shared
`ArrowApplyFacts.app_pure`. Its three remaining routing helpers concern
arbitrary state arrows and establish transformed application laws; they are
not consequences of lift preservation for base arrows.

Over option the carrier becomes `arr (A * S) (option (B * S))`: failure has
no final state. Transformer order matters. Read Core, law modules, then
[concrete tests](../../Taxonomy/Arrows/Tests/CONTEXT.md). Generic proofs are
algebraic, not inspections of a concrete relation or SP carrier.
