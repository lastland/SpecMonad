# SP observations context

Parent: [effect observations](../CONTEXT.md).
Related: [base specifications](../../BaseSpecMonads/CONTEXT.md),
[arrows](../../Arrows/CONTEXT.md), and [WP observations](../WP/CONTEXT.md).
Details: [README, SP observations](../../README.md#sp-side--effectobservationssp).

## Purpose and scope

These modules define strongest-postcondition observations, their morphism laws,
and triples. They cover the four base-monad readings and the arrow-derived
ASP/DSLP presentation. Cross-observation taxonomy lives in the parent directory.

## Established terms and definitions

- For the relation `R s r` selected by an observation, **ASP** reads
  `exists s, pre s /\ R s r`; **DSLP** reads `forall s, R s r -> pre s`.
  **DSP** conjoins those readings; **ASLP** disjoins them. The concrete
  [FullOutcomeObs definitions](StDivNonDet_SPStExc.v) package all four as
  well-formed base-monad values.
- **Over** means the observed postcondition implies the asserted postcondition;
  **Under** reverses that implication. [SPostArrObservation.v](SPostArrObservation.v)
  defines `tripleASP` / `tripleDSL` on observed arrows and proves the `*DefEq`
  characterizations against raw `pp2_over` / `pp2_under` transformers.
- [`runASP` / `runDSLP`](../../Arrows/SPostArrMonad.v) expose the arrow-derived
  monads at input `unit`. Effect files define `obsASP` using `relASP`, then
  `obsDSLP` using `asp_to_dslp`; see [the double-option case](StDivExcNonDet_SPostArr.v).

## Dependency boundaries

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
belongs to [DSPMonad.v](../../BaseSpecMonads/DSPMonad.v) and
[ASLPMonad.v](../../BaseSpecMonads/ASLPMonad.v): full-outcome proofs use
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
