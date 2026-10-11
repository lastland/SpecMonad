# Tests context

Parent: [Code](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md). Everything here is in the normal build and
is a leaf of the dependency graph; [Checks](../Checks/CONTEXT.md) is the
separate opt-in assumption audit.

## Generic arrow-derived monad regression

[ArrowMonadRegression.v](ArrowMonadRegression.v) protects the generic
arrow-derived monad and its application-law contract. It imports
[Arrow.v](../Lib/Arrow/Arrow.v), [ArrowApplyFacts.v](../Lib/Arrow/ArrowApplyFacts.v),
[ArrowMonad.v](../Lib/Arrow/ArrowMonad.v), ITree's monad laws,
and Coq equality infrastructure, without importing any specification carrier.

### What the regression establishes

- `CoreFactDependencies` checks `first_constant` and `pure_comp_ext` with
  core laws and explicit pure congruence, without application operations or
  laws. `StaticApplicationDependencies` checks constant application with
  only its fixed-arrow equation and core laws, without application laws.
- `WrongIndex.t A B := (bool -> A) -> bool -> B` supplies an arrow with
  proved core laws and an application operation that selects the stored
  arrow at `negb i`.
- `fixed_application` shows that this operation satisfies fixed-arrow
  application. `right_identity_fails` shows that this alone does not make
  the derived bind lawful.
- `application_contract_rejects_wrong_index` proves that the full
  `ArrowApplyLaws` contract rejects this implementation, using `app_unit`.
- `GenericResolution` checks `MonadLawsE` and `Eq1Equivalence` resolution for
  the exact `Monad_Arrow` operations and explicit `Eq1_Arrow`, for every
  fixed input type `I`.

### Reading and build membership

Read the application fields in `Arrow.v`, then `WrongIndex`, then
`GenericResolution`. The regression is listed in
[_CoqProject](../_CoqProject), so it belongs to the normal build.

The concrete instance checks below serve a different scope:
[ArrowMonadInstances.v](ArrowMonadInstances.v) and
[ArrowTransformerInstances.v](ArrowTransformerInstances.v)
check concrete carriers, dictionary reuse, and option/state stacks.
[Checks](../Checks/CONTEXT.md) is the separate opt-in assumption audit.

## Concrete arrow instance checks

Start with [SPostArrInfrastructure.v](SPostArrInfrastructure.v) for the
standalone property-only arrow checks. It imports none of the SP monad files and
checks `ArrowLaws`, `ArrowChoiceLaws`, and `ArrowApplyLaws` for all four flavours
implemented in [SPostArr.v](../SP/SPostArr.v) and [DSPASLPArr.v](../SP/DSPASLPArr.v). Its semantic regressions distinguish
DSP composition from raw forward transformer composition and exercise binary
state-over-option bind at a non-unit input, retaining that input, threading
the intermediate state, and propagating `None` without a final state.

[ArrowMonadInstances.v](ArrowMonadInstances.v) checks named `Monad`,
`Eq1Equivalence`, and `MonadLawsE` dictionaries that specialize
[ArrowMonad.v](../Lib/Arrow/ArrowMonad.v). Agreement lemmas compare compact
return/bind formulas with the exact derived operations. Resolution checks cover
`Rel`, the property-only ASP/DSLP carriers, and the other specification arrows,
including base/option/state/state-over-option layers with non-unit inputs.
The relational coverage serves both `asp` and `dslp` readings of the same
carrier; neither reading needs its own monad dictionary. The state-over-option
monad dictionaries of `ASPMonad.v` and `DSLPMonad.v` use explicit generic law
witnesses. `CanonicalSP` in `ArrowMonadInstances.v` compares canonical and
compatibility application/bind, checks dictionary identity, and exercises a
state update followed by propagated failure, read through the compatibility
relation `ASP_rel`.

[ArrowTransformerInstances.v](ArrowTransformerInstances.v) checks `optionRel`,
relational state-over-option arrows, the monad-view `progRelM` / `nditRelM`
stacks, and double-option application laws. Both SP readings reuse the existing
`Rel` operations and generic stack laws. The file depends on the generic arrow
transformers and [TransformerLaws.v](../Lib/Monad/TransformerLaws.v).

Its `PropertyEquality` module checks that property-only equality is
definitionally pointwise transformer iff, resolves all three base law packages,
and exercises `app_ext` and `Proper_bind` with semantic hypotheses for ASP and
DSLP. `Rel` keeps `Rel_eq`. The [semantic examples](#checked-sp-arrow-clients)
exercise the direct-Rel conversions and their higher-order application behavior.
Plain definitions register no helper instances: `:= _` checks automatic
resolution; explicit generic applications check specialization.

The generic contract is tested in
[ArrowMonadRegression.v](ArrowMonadRegression.v), including
an application satisfying the fixed-arrow law but breaking monad right identity.
This directory checks that concrete specification instances use that contract.

## Checked SP arrow clients

[SPostArrExamples.v](SPostArrExamples.v) exercises the public operations of
[SPostArr.v](../SP/SPostArr.v) and the operation-preserving conversions in
[SPostArrEquiv.v](../SP/SPostArrEquiv.v), using the generic option/state arrows.
The base conversions are `ASP_rel` / `relASP` and `DSLP_rel` / `relDSLP`.
`ASP_rel` and `DSLP_rel` both recover a `Rel` value. [RelSPostArr.v](../Relational/RelSPostArr.v)
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
resolution checks are the instance checks above.
