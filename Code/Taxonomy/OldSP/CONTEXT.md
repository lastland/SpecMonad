# Earlier SP presentation context

Parent: [Taxonomy context](../CONTEXT.md).
Current counterparts: [base specifications](../BaseSpecMonads/CONTEXT.md) and
[SP observations](../EffectObservations/SP/CONTEXT.md).
Details: [README, OldSP](../README.md#10-oldsp).

## Purpose and scope

This directory preserves the earlier reading-based SP presentation, its
rewriting rules, examples, and obstruction results. The current development
supersedes its main presentation, but its no-go theorems retain mathematical
value beyond that history.

## Established terms and definitions

- [OldSPObservations.v](OldSPObservations.v) defines additive and multiplicative
  transformers (`AdditiveSP`, `MultiplicativeSP`) and the corresponding
  `SPPure` / `PureSPM`, `SPStExc` / `ProgSPM`, and product `ProgSPB` monads.
- A **reading** interprets an already observed value. `obsSP` produces one
  value; `spASP`, `spDSLP`, `spDSP`, and `spASLP` read it as the four SP
  transformers. `tripleSPm` takes both `read` and `obs` explicitly.
- The same file retains `AsSPObs`, `tripleSP`, and the `readSP` / `readSPM`
  and `readJoin` / `readMeet` machinery. Its vocabulary is local: names such
  as `SPStExc` need not denote the current carriers. `SPredT` and `ordSP`
  occur only in commented-out historical experiments; they are not compiled
  or exported.
- The four `no_ProgSP_for_obsDSP`, `no_ProgSPM_for_obsDSP`,
  `no_ProgSP_for_obsASLP`, and `no_ProgSPM_for_obsASLP` results rule out
  representing those readings directly in the earlier additive/multiplicative
  carriers. They do not rule out the current DSP/ASLP monads.

## Dependency and build boundaries

Exactly three modules here are listed in [Code/_CoqProject](../../_CoqProject):

- [OldSPObservations.v](OldSPObservations.v): earlier carriers and observations.
- [OldIncorrectnessRewritingRules.v](OldIncorrectnessRewritingRules.v): rules
  over the earlier `tripleSP` presentation.
- [OldExamplePrograms.v](OldExamplePrograms.v): example theorems using those
  triples and shared [ExampleProgramDefs.v](../ExampleProgramDefs.v) programs.

[Observation.v](Observation.v) and [NonDetObservation.v](NonDetObservation.v)
are excluded reference modules. `Observation.v` contains an `Admitted`;
that admission is outside the build manifest. This mixed status differs from
`Taxonomy/deprecated/`, whose modules are all excluded.

The built presentation imports current computation, specification, arrow, and
WP observation modules. It is not the dependency foundation for the current
SP specification layer.

## Semantic traps

- Earlier `obsRel` / `obsSP` readings of `stdivexcnd` select terminating
  outcomes: `Some None` represents an exception; outer divergence is omitted.
- A shared `S -> Prop` precondition matters for `Under` triples. Replacing
  it with independent per-state judgments changes the quantifier structure;
  the commented-out historical example `progSP_under_not_point` in
  `OldSPObservations.v` illustrates this distinction. It is not a compiled
  theorem.
- The no-go results explain the limitations of a forward reading-based
  construction. Current [DSP](../BaseSpecMonads/DSPMonad.v) and
  [ASLP](../BaseSpecMonads/ASLPMonad.v) recover relations when defining bind.

## Reading order

Read the [README explanation](../README.md#10-oldsp) first. In
`OldSPObservations.v`, locate the reading or no-go theorem relevant to the
question rather than following every historical experiment. Continue to the
built rewriting rules or examples for clients; use the excluded modules only
when tracing the older observation style.
