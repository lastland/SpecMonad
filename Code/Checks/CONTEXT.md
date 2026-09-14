# Checks

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and audit scope

[Assumptions.v](Assumptions.v) is a console audit of selected proof
dependencies. It imports existing theorems and uses `Print Assumptions`
and `Check`; its output concerns only the named declarations.

The selected reports cover:

- All 13 [computation-owned raw outcome laws](../Taxonomy/ComputationMonads/CONTEXT.md#raw-outcome-law-interface):
  five single-option return/bind and primitive laws in
  [StExcNonDet.v](../Taxonomy/ComputationMonads/StExcNonDet.v), `outcomes_diverge`
  in [StDivNonDet.v](../Taxonomy/ComputationMonads/StDivNonDet.v), and seven
  double-option return/bind and primitive laws in
  [StDivExcNonDet.v](../Taxonomy/ComputationMonads/StDivExcNonDet.v).
- The four double-option WP return laws `obsDWP_ret`, `obsDWLP_ret`,
  `obsAWP_ret`, and `obsAWLP_ret` in
  [StDivExcNonDet_WStExc.v](../Taxonomy/EffectObservations/WP/StDivExcNonDet_WStExc.v).
  Their `Check` commands use `bool` state and `0 : nat`, exercising the
  independent state/result types supported by `WPureMonad.retP S a`.
- The 16 shared structural equations in
  [RelArrowCoherence.v](../Classes/RelArrowCoherence.v) and their eight concrete
  `ArrowLaws` / `ArrowChoiceLaws` instances across the property-only and coupled
  SP presentations.
- `rel_state_option_bind` in
  [RelArrowCoherence.v](../Classes/RelArrowCoherence.v) and `asp_to_dslp_bind`
  in [SPostArrMonad.v](../Taxonomy/Arrows/SPostArrMonad.v).
- ASP/DSLP bind laws and examples for state, exceptions, and nondeterminism
  in [StExcNonDet_SPostArr.v](../Taxonomy/EffectObservations/SP/StExcNonDet_SPostArr.v),
  and state, divergence, and nondeterminism in
  [StDivNonDet_SPostArr.v](../Taxonomy/EffectObservations/SP/StDivNonDet_SPostArr.v).
- Representative deterministic ITree and double-option bind laws from
  [StDivITree_SPostArr.v](../Taxonomy/EffectObservations/SP/StDivITree_SPostArr.v)
  and [StDivExcNonDet_SPostArr.v](../Taxonomy/EffectObservations/SP/StDivExcNonDet_SPostArr.v).
- DSP/ASLP ordered-bind counterexamples, non-monotonicity theorems, and
  arbitrary-bind impossibility theorems for Boolean state in
  [SPBindOrderCounterexample.v](../Taxonomy/BaseSpecMonads/SPBindOrderCounterexample.v).

## Semantic regressions versus audit commands

The [raw semantic regressions](../Taxonomy/ComputationMonads/CONTEXT.md#semantic-regressions)
live beside the computation laws: empty prefixes block, exceptions and
divergence survive empty continuations, and `pickP` at `Empty_set` blocks.
The double-option arrow examples `raiseP_obs_retained` and `spinP_obs_invisible`
in [StDivExcNonDet_SPostArr.v](../Taxonomy/EffectObservations/SP/StDivExcNonDet_SPostArr.v)
check which outcomes the terminating slice retains. These are proofs in the
normal build, not new audit commands. The audit's WP `Check` commands only
instantiate existing theorem types.

## Build boundary and reading

`Assumptions.v` is deliberately absent from [_CoqProject](../_CoqProject).
The maintained [Makefile](../Makefile) keeps `all` as the default goal and
provides opt-in `make check`: it builds the normal build (the audit's
dependency closure lies inside it) and invokes Coq on the audit explicitly.
Its `clean` rule also removes audit outputs that ordinary `VFILES` cleanup
would miss.

Read `Assumptions.v` for the exact report selection and the `check` target
of [Makefile](../Makefile) for execution membership. Consult the current output
for theorem dependencies rather than inferring them from imports. The target
reports assumptions; it does not compare them against an allowlist.

Related contexts: [Classes](../Classes/CONTEXT.md),
[generic regressions](../Classes/Tests/CONTEXT.md), and
[concrete Taxonomy tests](../Taxonomy/Arrows/Tests/CONTEXT.md).
Those regression/instance checks belong to the normal build, unlike this audit.
