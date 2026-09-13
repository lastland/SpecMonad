# SP observations context

Parent: [observations](../CONTEXT.md). Targets: [base specs](../../BaseSpecMonads/CONTEXT.md)
and [arrows](../../Arrows/CONTEXT.md).

## Earlier well-formed-monad clients

- StDivExcNonDet_SPStExc selects terminating outcomes of the double-option
  computation, including exceptions, and targets OldMonads' four flavours.
- StDivNonDet_SPStExc/FullOutcomeObs retains the single-option divergence
  outcome; StDivNonDet_SPSt/TermSliceObs selects normal returns only.
- DivNonDet_SPPure/PureObs targets the four pure old carriers;
  RdDivNonDet_RdSPPure applies those observations per reader environment.

For relation R, ASP is existential pre-and-reachability, DSLP universal
reachability-implies-pre, DSP their conjunction, and ASLP their disjunction.
DSP/ASLP target binds recover relations; they are not simple forward composition.
Pure DSP/ASLP collapse to ASP/DSLP, and reader collapse is per environment.
Determinism does not imply unique predecessors, so WP collapse does not imply
SP collapse. Full and terminating-slice observations must not be conflated.

## Arrow-derived clients

SPostArrObservation shares the property-only ASP/DSLP observation interface
and Taxonomy-style judgments. StDivITree_SPostArr, StExcNonDet_SPostArr,
StDivNonDet_SPostArr, and StDivExcNonDet_SPostArr instantiate it using each
computation's outcome relation. RawStOpt_SPostArr shares single-option outcome
facts. Generic relational bind facts and SPostArrMonad select the exact target
arrow dictionaries; neither adds a relation field to property-only values.

SP Over includes observed in asserted post; Under includes asserted in observed.
Old in-monad targets can need an inhabited precondition for ASP Under and an
inhabited complement for DSLP Over. Preserve those hypotheses. Read outcomes
→ selected target/operations → preservation → triples → comparisons/examples.

- Computation-specific files depend on a source model and its specification
  target. Base SP well-formedness and operations remain in the specification layer.
- [RawStOpt_SPostArr.v](RawStOpt_SPostArr.v) shares raw return/bind laws for
  the single-option nondeterministic models. `SPostArrObservation.v` depends
  only on specification arrows, even though it lives in this directory.
- [RdPureObs](RdDivNonDet_RdSPPure.v) reuses [PureObs](DivNonDet_SPPure.v)
  environment by environment. Comparisons of the stateful readings belong to
  the [parent taxonomy layer](../CONTEXT.md).

## Base DSP/ASLP bind proofs

The DSP/ASLP bind proofs in [FullOutcomeObs](StDivNonDet_SPStExc.v) and
[TermSliceObs](StDivNonDet_SPSt.v) combine computation `outcomes_bind` with
specification bind normalization and relation congruence. Recovery reasoning
belongs to [OldMonads/DSPMonad.v](../../BaseSpecMonads/OldMonads/DSPMonad.v) and
[OldMonads/ASLPMonad.v](../../BaseSpecMonads/OldMonads/ASLPMonad.v): full-outcome proofs use
`dsp_comp_recov_option` / `aslp_comp_recov_option`, while terminating-slice
proofs apply specialized recovery through `StDSP.comp_cong`. Neither proof
reconstructs recovery probes; both retain their own outcome relation.

## Semantic traps

- [StDivNonDet_SPStExc.v](StDivNonDet_SPStExc.v) retains `None` as divergence.
  [StDivNonDet_SPSt.v](StDivNonDet_SPSt.v), under `TermSliceObs`, drops it and
  targets outcomes `A * S`.
- [StDivExcNonDet_SPStExc.v](StDivExcNonDet_SPStExc.v) reads raw outcomes at
  `Some r`: outer divergence disappears, while `r = None` is an exception.
  Its [arrow counterpart](StDivExcNonDet_SPostArr.v) selects the same slice.
- [StDivITree_SPostArr.v](StDivITree_SPostArr.v) observes convergence to `Ret r`;
  `Ret None` is a terminating exception. The two single-option arrow files
  read `None` as [exception](StExcNonDet_SPostArr.v) or
  [divergence](StDivNonDet_SPostArr.v), respectively.
- Pure DSP/ASLP collapse to ASP/DSLP, with named `obsDSP_is_obsASP` and
  `obsASLP_is_obsDSLP` lemmas. The reader lift inherits this collapse; it
  does not supply a transformer over a shared set of environments.
- Deterministic computation need not have unique predecessors. Deterministic
  WP collapse therefore does not justify identifying ASP and DSLP.
- Raw `*spec` comparisons and in-monad targets have different contracts.
  The latter use [generic embeddings](../../BaseSpecMonads/NewGaloisConnections.v)
  and, in some directions, orders at one precondition plus side conditions.

## Reading order

Read the chosen outcome relation first, then its `obs*` definitions and
return/bind laws. For arrow clients, read `SPostArrMonad.v` and the shared
judgments before an effect file. Finish with its triples/examples and the
matching [taxonomy comparison](../CONTEXT.md); use the
[README](../../README.md#arrow-derived-aspdslp-observations) for presentation details.
