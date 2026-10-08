# Checked SP arrow clients

Parent: [Arrows context](../CONTEXT.md). Related:
[concrete tests](../Tests/CONTEXT.md),
[Triples](../../Triples/CONTEXT.md).

[SPostArrExamples.v](SPostArrExamples.v) exercises the public operations of
[SPostArr.v](../SPostArr.v) and the operation-preserving conversions in
[SPostArrEquiv.v](../SPostArrEquiv.v), using the generic option/state arrows.
The base conversions are `ASP_rel` / `relASP` and `DSLP_rel` / `relDSLP`.
`ASP_rel` and `DSLP_rel` both recover a `Rel` value. [RelSPostArr.v](../RelSPostArr.v)
computes its `asp` and `dslp` readings without storing a transformer alongside
the relation.

The public round trips use the selected property-only `arrow_eq` or `Rel_eq`.
Operation-preservation results use the destination's selected equality;
`morphism_proper` ensures that each conversion respects source equivalence.

Read `asp_roundtrip_many_to_one` / `dslp_roundtrip_many_to_one` first: a
deterministic many-to-one arrow still distinguishes existential ASP from
universal DSLP. `empty_domain` and `unreachable_output` expose DSLP's vacuity.
Then follow the option-failure/choice examples and
`state_roundtrip_threads_updates` for propagation and state threading through
`state_option_asp_to_rel` / `state_option_asp_from_rel`.
`state_application_conversion` checks that higher-order application converts
the stored arrow as well as the surrounding stack, using
`state_option_asp_to_rel_morphism`. The relational side reuses the existing
`Rel` operations and their generic option/state dictionaries. The later
application examples exercise precomposition, postcomposition, and captured input.

These are semantic clients of specification arrows. Computation-specific
readings and worked program triples live in Triples; dictionary
resolution checks live in the sibling tests directory.
