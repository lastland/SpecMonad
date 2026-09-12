# Earlier SP presentation context

Parent: [Taxonomy](../CONTEXT.md). Current counterparts:
[base specifications](../BaseSpecMonads/CONTEXT.md) and [SP observations](../EffectObservations/SP/CONTEXT.md).

Exactly three modules are normally built: OldSPObservations,
OldIncorrectnessRewritingRules, and OldExamplePrograms. Observation and
NonDetObservation are excluded reference files; Observation contains an
admission outside the manifest. Unlike this mixed directory, deprecated is
wholly excluded. Consult both the manifest and Coq comment boundaries.

OldSPObservations defines additive/multiplicative transformers, SPPure/PureSPM,
state-option SPStExc/ProgSPM, and their product ProgSPB. These names are local,
not aliases for current raw carriers. obsSP packages terminating reachability;
spASP/spDSLP/spDSP/spASLP read the same observed value. tripleSPm takes read
and obs explicitly; tripleSP consumes a transformer observation. OriginalTripleSP
has its own Correct/Incorrect vocabulary. Earlier rules/examples use tripleSP,
not the current tripleASP interface.

The four no_ProgSP/ProgSPM_for_obsDSP/ASLP theorems refute the specified older
direct readings, not every possible reading, the product, or current DSP/ASLP
monads. Current stateful DSP/ASLP binds recover relations.

The AspConjugation block through SPred_under_empty_pre_fails is commented out:
ProgSPObs, SPredObs, SPredT, ordSP, and progSP_under_not_point there are not
exported results. Its shared-versus-independent precondition discussion does
not supply compiled theorems. In particular, changing a shared `S -> Prop`
precondition to independent per-state judgments changes the quantifiers in
Under triples; the commented example illustrates this, but does not prove it.
Active double-option observations omit outer divergence and retain exceptions.
This layer imports current modules; it is not the foundation of the base SP
layer. Read the historical README discussion, then the relevant active
reading/no-go result and manifest-listed clients.
