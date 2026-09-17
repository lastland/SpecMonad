# Effect observations context (main)

Parent: [Taxonomy context](../CONTEXT.md).
Inputs: [computation monads](../ComputationMonads/CONTEXT.md).
Targets: [base specification monads](../BaseSpecMonads/CONTEXT.md).

## Purpose and scope

This layer interprets computations as specifications and compares the resulting
transformers and triples. [SP](SP/CONTEXT.md) and [WP](WP/CONTEXT.md) define
observations; the three comparison files here organize their taxonomy.
File names identify a source model and target indexing, but do not by themselves
say whether divergence remains an explicit specification outcome.

## Observation contracts

- Read the chosen outcome relation before `obsASP`, `obsDSLP`, `obsDSP`, or
  `obsASLP`. The [full-outcome SP file](SP/StDivNonDet_SPStExc.v) retains
  divergence, while the [double-option SP file](SP/StDivExcNonDet_SPStExc.v)
  selects the terminating slice, including exceptions.
- WP observations quantify over possible executions from one initial state.
  Their total/liberal distinction controls how they treat divergence; see
  [StDivExcNonDet_WStExc.v](WP/StDivExcNonDet_WStExc.v).
- SP triples compare postconditions: `Over` is observed implies asserted;
  `Under` is asserted implies observed. WP `SubsetOf` / `SupersetOf` compare
  asserted and computed preconditions instead. The deterministic WP file uses
  its own `Under` / `Over` constructors; qualify names when mixing modules.
- Return/bind preservation and triple-refinement equivalences are separate
  results. All five SP files provide `obs*_ret` / `obs*_bind`; WP coverage
  varies by file. Do not infer a theorem solely from the observation's type.

## Comparison entrypoints

- [Taxonomy_StDivExcNonDet_StExc.v](Taxonomy_StDivExcNonDet_StExc.v) compares
  the double-option WP and SP readings: inclusions, contrapositive pairs,
  triple implications, `Section GaloisConnection`, and `WithdrawExample`.
- [Taxonomy_StDivNonDet_StExc.v](Taxonomy_StDivNonDet_StExc.v) contains
  `TaxonomyFullOutcome`, the SP comparisons that retain divergence, including
  `DSP_conjunction` and `ASLP_disjunction`.
- [Taxonomy_StDivNonDet_St.v](Taxonomy_StDivNonDet_St.v) contains
  `TaxonomyStDivNonDetWSt` for WP on `stdivndNE` and
  `TaxonomyStDivNonDetSPSt` for terminating-slice SP on unrestricted `stdivnd`.

In the double-option comparison, `dwlp_slice` and `awp_slice` expose the same
terminating relation used by SP. `dwlp_asp` identifies demonic-liberal WP
`SubsetOf` with ASP `Over`; `awp_dslp` identifies angelic-total WP `SupersetOf`
with DSLP `Under`. These are equivalences of the specified triples, not a
blanket identification of the observation carriers.

## Conditions and dependency boundaries

- Demonic-to-angelic WP inclusions for `stdivexcnd` require an inhabited
  outcome set. The state-only WP comparison gets this from `stdivndNE`.
  An empty outcome set is not a divergent execution.
- Keep orders explicit: `ordWSt` / `ordWStExc` use forward implication,
  unlike base `WP_le`. In-monad SP targets may require an order at one
  precondition and a side condition; see [NewGaloisConnections.v](../BaseSpecMonads/NewGaloisConnections.v).
- Concrete readings belong here, not in the specification carriers.
  The import graph is not completely separated: the double-option SP file
  imports its WP counterpart, and the reader SP file reuses the pure SP file.
- Comparison files with both halves import SP modules after their WP sections.
  Preserve name resolution when changing that order; repeated `obs*`, `pre`,
  `post`, and approximation constructors do not always denote the same objects.

## Reading order

Follow the computation, target, selected outcomes, preservation laws, and
triple definition before the corresponding comparison. Shared programs live in
[ExampleProgramDefs.v](../ExampleProgramDefs.v), local examples with their
observations. `WithdrawExample` contrasts angelic WP coverage (each input has
an acceptable output) with ASP bug presence (each asserted output has some input).
