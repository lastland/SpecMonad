# Checked SP arrow clients

Parent: [Arrows context](../CONTEXT.md). Related:
[concrete tests](../Tests/CONTEXT.md),
[SP observations](../../EffectObservations/SP/CONTEXT.md).

[SPostArrExamples.v](SPostArrExamples.v) exercises the public operations of
[SPostArr.v](../SPostArr.v) and the operation-preserving conversions in
[SPostArrEquiv.v](../SPostArrEquiv.v), using the generic option/state arrows.

Read `asp_roundtrip_many_to_one` / `dslp_roundtrip_many_to_one` first: a
deterministic many-to-one arrow still distinguishes existential ASP from
universal DSLP. `empty_domain` and `unreachable_output` expose DSLP's vacuity.
Then follow the option-failure/choice examples and
`state_roundtrip_threads_updates` for propagation and state threading.
`state_application_conversion` checks that higher-order application converts
the stored arrow as well as the surrounding stack; the later application
examples exercise precomposition, postcomposition, and captured input.

These are semantic clients of specification arrows. Computation-specific
readings and worked program triples live with the SP observations; dictionary
resolution checks live in the sibling tests directory.
