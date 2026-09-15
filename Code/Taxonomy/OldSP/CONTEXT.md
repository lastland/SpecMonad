# Earlier SP presentation context (main)

Parent: [Taxonomy context](../CONTEXT.md).
Current counterparts: [base specifications](../BaseSpecMonads/CONTEXT.md) and
[SP observations](../EffectObservations/SP/CONTEXT.md).

## Purpose and scope

This directory preserves the earlier reading-based SP presentation, rewriting
rules, examples, and representation obstructions. It is not all excluded
history, nor is every declaration-looking passage an active definition.
Use [Code/_CoqProject](../../_CoqProject) and Coq comment boundaries together.

## Manifest boundary

Exactly three files here are listed in the current manifest:

- [OldSPObservations.v](OldSPObservations.v): earlier carriers, readings,
  observations, triples, and no-go results.
- [OldIncorrectnessRewritingRules.v](OldIncorrectnessRewritingRules.v): rules
  over `tripleSP obsASP`, rather than the current `tripleASP` interface.
- [OldExamplePrograms.v](OldExamplePrograms.v): earlier triple examples using
  shared programs from [ExampleProgramDefs.v](../ExampleProgramDefs.v).

[Observation.v](Observation.v) and [NonDetObservation.v](NonDetObservation.v)
are excluded reference files. `Observation.v` contains an `Admitted` outside
the manifest. Unlike this mixed directory, `Taxonomy/deprecated/` is wholly
excluded. Manifest inclusion alone does not establish successful compilation
or the assumptions of a result.

## Existing vocabulary and contracts

- `OldSPObservations.v` defines `AdditiveSP` and `MultiplicativeSP`, the
  healthy `SPPure` / `PureSPM` carriers, and their state/option stacks
  `SPStExc` / `ProgSPM`. These names are local to this presentation:
  its `SPStExc` is a transformer stack, not the current raw shared-precondition carrier.
- `obsSP` packages the terminating reachability relation through `ofSet`.
  `spASP`, `spDSLP`, `spDSP`, and `spASLP` then read the same observed value.
  `tripleSPm` takes both `read` and `obs` explicitly; top-level `tripleSP`
  instead consumes a transformer-valued observation directly.
- `readSP` / `readSPM` and `ofSet` / `ofCoSet` support additive and
  multiplicative readings. `ProgSPB` is their product at the stack level;
  `SPMonadObsB.readMeet` / `SPMonadObsB.readJoin` conjoin/disjoin its readings.
- `OriginalTripleSP.AsSPObs` exposes a transformer from several older
  observation result types. That module's `Correct` / `Incorrect` constructors are
  distinct from the top-level `Under` / `Over` vocabulary.

## Obstructions and historical experiments

`no_ProgSP_for_obsDSP`, `no_ProgSPM_for_obsDSP`, `no_ProgSP_for_obsASLP`,
and `no_ProgSPM_for_obsASLP` rule out representing the `progEx` readings via
the specified `readSP` / `readSPM` carriers. They do not rule out all possible
readings, the product construction, or the current DSP/ASLP monads. The
[DSP](../BaseSpecMonads/DSPMonad.v) and [ASLP](../BaseSpecMonads/ASLPMonad.v)
binds recover relations rather than use these older forward constructions.

The block beginning `(*Section AspConjugation.` and ending after
`SPred_under_empty_pre_fails` is commented out. It includes `ProgSPObs`,
`SPredObs`, `SPredT`, `ordSP`, and `progSP_under_not_point`; these are not
exported declarations. Their discussion illustrates why independent per-state
preconditions differ from a shared `S -> Prop` precondition, especially for
under-approximation. Do not cite those passages as compiled theorems.

## Reading guidance and dependencies

Start with the [README's historical discussion](../README.md), then locate
the relevant active reading or no-go result instead of following every experiment.
The active `obsRel` / `obsSP` omit outer divergence from `stdivexcnd` and retain
exceptions (`Some None` in the raw computation, `None` in the observed slice).
This presentation imports current computation, specification, arrow, and WP
modules; it is not the foundation of the current base SP layer. Use the two
manifest-listed client files for older rules/examples and the current counterparts
above for new work.
