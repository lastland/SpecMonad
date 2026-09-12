# Computation monads context

Parent: [Taxonomy](../CONTEXT.md). Consumers: [observations](../EffectObservations/CONTEXT.md).

These modules own computations and outcome relations, not specification
well-formedness or reading equivalences. TransformerLaws is generic ExtLib
infrastructure for option/state/reader stacks and is also used by specifications.
Avoid duplicating library laws or computation-owned raw outcome laws in clients.

StDivITree uses deterministic interaction trees; convergence and divergence
require their actual ITree semantics, not structural equality. StExcNonDet
models state/exception nondeterminism; StDivNonDet models state/divergence;
StDivExcNonDet has two option layers, separating normal returns, exceptions,
and divergence. DivNonDet and RdDivNonDet supply pure and reader versions.

For stdivexcnd at an initial state, outer None is divergence, Some None is
exception, and Some(Some(a,s)) is normal return. A terminating slice omits only
the outer None. In a single-option model, None's meaning comes from the model.
Nonempty variants (including stdivndNE/stdivexcndNE) exclude empty outcome
sets, not divergence; preserve their hypotheses in strictness/top theorems.

Read carrier/operations → outcome definition → return/bind laws → observation.
The existence of computation laws does not establish an arbitrary specification
order's bind monotonicity. Use the manifest for active source membership.
