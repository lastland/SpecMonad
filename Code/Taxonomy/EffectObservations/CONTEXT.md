# Effect observations context

Parent: [Taxonomy](../CONTEXT.md). Read [computation outcomes](../ComputationMonads/CONTEXT.md)
and [target specifications](../BaseSpecMonads/CONTEXT.md) first.

[SP](SP/CONTEXT.md) and [WP](WP/CONTEXT.md) map computations to specifications;
the parent files compare readings, inclusions, contrapositive pairs, and triples.
Arrow-derived SP clients coexist with the earlier OldMonads-targeted clients.
Return/bind preservation refers to actual selected dictionaries, not just types.

Taxonomy_StDivExcNonDet_StExc compares the terminating double-option slice,
including exceptions. Taxonomy_StDivNonDet_StExc retains full single-option
outcomes. Taxonomy_StDivNonDet_St compares terminating SP slices with WP over
the nonempty computation fragment. Preserve nonemptiness assumptions;
empty outcome sets are not divergent executions.

SP Over means observed implies asserted; Under reverses it. WP local triple
constructors/orders may reverse that direction and have different argument
positions. In-monad SP targets can require a fixed-precondition order and side
conditions. Always inspect definitions before transporting a theorem.

The double-option wp/sp equivalences identify specified triples, not all
carrier bundles. WithdrawExample contrasts angelic WP coverage with ASP bug
presence. Shared programs are in ExampleProgramDefs. Read observation bodies
and outcome cases before laws, comparisons, and examples; qualify repeated
obs/pre/post names when mixing files.
