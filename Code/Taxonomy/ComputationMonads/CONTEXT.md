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
These modules define computations, effect operations, monad laws, and raw
outcome laws. They supply the concrete semantics consumed by
[effect observations](../EffectObservations/CONTEXT.md).

For stdivexcnd at an initial state, outer None is divergence, Some None is
exception, and Some(Some(a,s)) is normal return. A terminating slice omits only
the outer None. In a single-option model, None's meaning comes from the model.
Nonempty variants (including stdivndNE/stdivexcndNE) exclude empty outcome
sets, not divergence; preserve their hypotheses in strictness/top theorems.

Read carrier/operations → outcome definition → return/bind laws → observation.
The existence of computation laws does not establish an arbitrary specification
order's bind monotonicity. Use the manifest for active source membership.

- [`SetM A := A -> Prop`](StExcNonDet.v) represents a set of outcomes;
  return is a singleton and bind existentially composes sets.
- [`stexcnd`](StExcNonDet.v) and [`stdivnd`](StDivNonDet.v) both use
  `stateT S (optionT SetM)`. `None` means an exception for `stexcnd`, which
  supplies `raiseP`/`catchP`; it means divergence for `stdivnd`, which supplies
  `divergeD`, `mayDiverge`, and `orD` without its own `MonadExc` instance.
- [`stdivexcnd`](StDivExcNonDet.v) uses two option layers. Its raw outcomes
  are `Some (Some (a, s'))` for return, `Some None` for exception, and
  outer `None` for divergence. `spinP` selects the divergent outcome.
- [`divexcnd`](DivExcNonDet.v) removes the state layer from the double-option
  stack: `optionT (optionT SetM)`. Its outcomes are `Some (Some a)` for return,
  `Some None` for exception, and `None` for divergence. `orP` is raw union,
  not the option transformer's left-biased choice.
- [`stdivitree`](StDivITree.v) uses `stateT S (optionT (itree void1))`.
  Returning `None` is an exception; divergence belongs to the underlying
  ITree behavior. Its base equality is `eutt eq`.
- [`divnd`](DivNonDet.v) removes state; [`rddivnd`](RdDivNonDet.v) adds
  `readerT R` to it. Reader outcomes contain no final environment, unlike
  state outcomes, which contain the final state.
- [`nonEmptyOutcomes` / `stdivndNE`](StDivNonDet.v) require an outcome at
  every initial state. The pure and reader modules have corresponding fragments.

## Raw outcome-law interface

The nondeterministic modules own the following full-outcome laws.
Each is a constructive pointwise `<->` statement at a raw outcome (and an
initial state for stateful models), rather than an equality of computations.

| Module | Laws | Scope |
|---|---|---|
| [StExcNonDet.v](StExcNonDet.v) | `outcomes_ret`, `outcomes_bind`, `outcomes_get`, `outcomes_put`, `outcomes_raise` | Shared single-option return/bind; state and exception primitives |
| [StDivNonDet.v](StDivNonDet.v) | `outcomes_diverge` | `divergeD` has exactly the outcome `None` |
| [StDivExcNonDet.v](StDivExcNonDet.v) | `outcomes_ret`, `outcomes_bind`, `outcomes_get`, `outcomes_put`, `outcomes_raise`, `outcomes_pickP`, `outcomes_spin` | Double-option return/bind and primitives |
| [DivExcNonDet.v](DivExcNonDet.v) | `outcomes_ret`, `outcomes_bind`, `outcomes_raise`, `outcomes_spin`, `outcomes_orP` | Stateless double-option return/bind, failure tokens, and raw union |

`StExcNonDet.outcomes_ret` / `outcomes_bind` name the shared raw dictionaries
of `stateT S (optionT SetM)`. The single-option `retP` / `bindP` and
`retD` / `bindD` convert to these operations definitionally. Clients reuse
these laws without choosing the same reading of `None`.

## Dependency boundaries

- Concrete stacks reuse ExtLib transformers and ITree laws. `StExcNonDet.v`
  supplies the shared `SetM` base used by the other nondeterministic models.
- [TransformerLaws.v](TransformerLaws.v) proves `Eq1`-generic option, state,
  and reader transformer laws from base `MonadLawsE` assumptions. It names
  no concrete computation monad, so [base specifications](../BaseSpecMonads/CONTEXT.md)
  can import it without depending on a concrete computation.
  Its `ord_optionT` and `bind_optionT_mono` separately lift an explicit
  reflexive order and simultaneous bind monotonicity through `optionT`.
- Observation-specific readings and triples belong in
  [SP](../EffectObservations/SP/CONTEXT.md) or [WP](../EffectObservations/WP/CONTEXT.md).
  Their slice and non-empty-carrier adapters derive from computation-owned
  laws instead of repeating raw stack normalization. The state-free
  [DivNonDet.outcomes_bind](DivNonDet.v) follows the same ownership pattern.

## Semantic traps

- The exception/divergence distinction for the single-option models is
  semantic, not enforced by distinct raw carriers. Qualify repeated operation
  names when several computation modules are imported.
- An empty outcome set is blocking: it is neither a return nor the explicit
  divergence token. `stdivndNE` excludes it; it does not require termination.
- Bind runs the continuation only after a normal return and propagates failure
  tokens unchanged. An empty prefix therefore blocks, but an empty continuation
  does not erase a preceding exception or divergence.
- State-over-option failure has no final state in its outcome.
- [`denote`](StDivExcNonDet.v) interprets `freeprog` using ITree handlers,
  `Leaf`, and `any_infinite`. ITree's state handler returns `(state, result)`;
  the ExtLib stack stores `(result, state)`, so the definition swaps them.

## Semantic regressions

The examples beside the computation laws check the raw semantics:

- [DivExcNonDet.v](DivExcNonDet.v): `success_continuation`,
  `raise_survives_empty`, `spin_survives_empty`, and `mixed_outcomes`.
- [StExcNonDet.v](StExcNonDet.v): `empty_prefix_blocks` and `raise_survives_empty`.
- [StDivNonDet.v](StDivNonDet.v): `diverge_survives_empty`.
- [StDivExcNonDet.v](StDivExcNonDet.v): `blockP_bind_blocks`, `raiseP_bind_empty`,
  `spinP_bind_empty`, and `pickP_Empty_set_blocks`.

The empty computations are local example definitions, not new model operations.
At the [double-option arrow observation](../EffectObservations/SP/StDivExcNonDet_SPostArr.v),
`raiseP_obs_retained` and `spinP_obs_invisible` separately check that the
terminating slice retains exceptions but omits divergence.

## Reading order

Start with `SetM` and the single-option raw laws in `StExcNonDet.v`, then the
divergence, double-option, or ITree model needed by the client. Follow the raw
laws into the observation's full-outcome reading or derived slice adapter.
Read non-empty fragments before the
[`WSt` observations](../EffectObservations/WP/StDivNonDet_WSt.v).
Read `TransformerLaws.v` when following a law instance through a stack;
use the [README](../README.md#2-computation-monads) for the complete effect table.
