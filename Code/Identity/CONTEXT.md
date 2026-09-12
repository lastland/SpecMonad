# Identity context

Parent: [Code](../CONTEXT.md). These pure developments have no effect stack.

[Identity.v](Identity.v)'s SPost maps a propositional precondition to a result
predicate implying it, without monotonicity. `theta m := SPost_ret m`;
Incorrect requires `achieves r -> r = m /\ presumes` for each r. Its final
attempted example ends in Abort, not a negative theorem.

[IdentityVariations.v](IdentityVariations.v) distinguishes:
- ContextFree: `exists γ, m γ = r /\ P γ`, hiding inputs per result.
- ContextFull: `m γ = r /\ P γ`, retaining each asserted input/result pair.
- ContextImplicit: `m = r /\ P` for a fixed value and propositional P.

Incorrect includes achieves in SP; Correct includes SP in the postcondition.
Correct_alt, weakening/disjunction/monotonicity, and agreement results have
module-specific quantifiers. Preserve the source spelling `Incorect`.
Read variations first; do not transfer claims between modules blindly.
Identity.v uses CoqHammer; variations is self-contained. Neither imports
Common/Taxonomy. Related: [Reader](../Reader/CONTEXT.md) and [ST](../ST/CONTEXT.md).
