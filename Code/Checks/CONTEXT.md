# Checks

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and audit scope

[Assumptions.v](Assumptions.v) is a console audit of selected proof
dependencies. It imports existing theorems and uses `Print Assumptions`
and `Check`; it does not define another specification model or prove that
the entire development is axiom-free.

The selected reports cover:

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
- DSP/ASLP ordered-bind counterexamples and non-monotonicity theorems in
  [SPBindOrderCounterexample.v](../Taxonomy/BaseSpecMonads/SPBindOrderCounterexample.v).

## Build boundary and reading

`Assumptions.v` is deliberately absent from [_CoqProject](../_CoqProject).
The maintained [Makefile](../Makefile) keeps `all` as the default goal and
provides opt-in `make check`: it builds the listed prerequisites and invokes
Coq on the audit explicitly. Its `clean` rule also removes audit outputs
that ordinary `VFILES` cleanup would miss.

Read `Assumptions.v` for the exact report selection and the `check` target
of [Makefile](../Makefile) for execution membership. The output reports
assumptions; the target does not compare them against an allowlist.

Related contexts: [Classes](../Classes/CONTEXT.md),
[generic regressions](../Classes/Tests/CONTEXT.md), and
[concrete Taxonomy tests](../Taxonomy/Arrows/Tests/CONTEXT.md).
Those regression/instance checks belong to the normal build, unlike this audit.
