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
- Raw return/bind laws belong to [StExcNonDet.v](../../ComputationMonads/StExcNonDet.v)
  for the shared single-option stack and
  [StDivExcNonDet.v](../../ComputationMonads/StDivExcNonDet.v) for the double-option
  stack. [StDivNonDet.v](../../ComputationMonads/StDivNonDet.v) owns `outcomes_diverge`.
  Full-outcome clients use these laws directly; slice clients derive adapters.
- [SPostArrObservation.v](SPostArrObservation.v) depends only on specification
  arrows, even though it lives in this directory.
- [DivExcNonDet_SPDivExc.v](DivExcNonDet_SPDivExc.v) observes the full raw
  outcomes of stateless `divexcnd` into `DSPDivExc` / `ASLPDivExc`.
  `obsDSP` reads `p /\ outcomes m o`; `obsASLP` reads `p \/ ~ outcomes m o`.
  Both preserve return and bind. The specification binds are monotone in both
  arguments. Divergence (`None`) and exceptions (`Some None`) remain distinct;
  raw-union choice gives DSP disjunction and ASLP conjunction.
- [RdPureObs](RdDivNonDet_RdSPPure.v) reuses [PureObs](DivNonDet_SPPure.v)
  environment by environment. Comparisons of the stateful readings belong to
  the [parent taxonomy layer](../CONTEXT.md).

## Derived slice facts

[TermSliceObs](StDivNonDet_SPSt.v) derives `outcomes_ret`, `outcomes_bind`, and
`outcomes_diverge` from the full raw laws at `Some r`, with `r : A * S`.
Its bind adapter keeps only normal intermediate returns.

[StDivExcNonDet_SPostArr.v](StDivExcNonDet_SPostArr.v) derives its local
`outcomes_bind` and primitive `outcomes_get` / `outcomes_put` / `outcomes_raise` /
`outcomes_pickP` facts at `Some r`, with `r : option (A * S)`. This adapter
retains exceptions while omitting outer divergence. Qualify computation laws
when similarly named slice facts are in scope.

## Base DSP/ASLP bind proofs

The DSP/ASLP bind proofs in [FullOutcomeObs](StDivNonDet_SPStExc.v) and
[TermSliceObs](StDivNonDet_SPSt.v) combine the raw or derived slice `outcomes_bind`
with specification bind normalization and relation congruence. Recovery reasoning
belongs to [DSPMonad.v](../../BaseSpecMonads/DSPMonad.v) and
[ASLPMonad.v](../../BaseSpecMonads/ASLPMonad.v): full-outcome proofs use
`dsp_comp_recov_option` / `aslp_comp_recov_option`, while terminating-slice
proofs apply specialized recovery through `StDSP.comp_cong`. Neither proof
reconstructs recovery probes; both retain their own outcome relation.
This specification-side recovery is separate from raw computation normalization.

## Semantic traps

- [StDivNonDet_SPStExc.v](StDivNonDet_SPStExc.v) retains `None` as divergence.
  [StDivNonDet_SPSt.v](StDivNonDet_SPSt.v), under `TermSliceObs`, drops it and
  targets outcomes `A * S`.
- [StDivExcNonDet_SPStExc.v](StDivExcNonDet_SPStExc.v) reads raw outcomes at
  `Some r`: outer divergence disappears, while `r = None` is an exception.
  Its [arrow counterpart](StDivExcNonDet_SPostArr.v) selects the same slice.
  The examples `raiseP_obs_retained` and `spinP_obs_invisible` check these
  two cases through `runASP`.
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

Read the computation-owned raw laws, the chosen outcome relation, and any
slice adapter before the `obs*` preservation proofs. For arrow clients, read
`SPostArrMonad.v` and the shared judgments before an effect file. Finish with
its triples/examples and the matching [taxonomy comparison](../CONTEXT.md); use the
[README](../../README.md#arrow-derived-aspdslp-observations) for presentation details.
