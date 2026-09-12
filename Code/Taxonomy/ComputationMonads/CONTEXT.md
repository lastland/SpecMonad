# Computation monads context

Parent: [Taxonomy context](../CONTEXT.md).
Details: [README, computation monads](../README.md#2-computation-monads).

## Purpose and scope

These modules define computations, their effect operations, and monad laws.
They supply the concrete semantics consumed by
[effect observations](../EffectObservations/CONTEXT.md).

## Established terms and definitions

- [`SetM A := A -> Prop`](StExcNonDet.v) represents a set of outcomes;
  return is a singleton and bind existentially composes sets.
- [`stexcnd`](StExcNonDet.v) and [`stdivnd`](StDivNonDet.v) both use
  `stateT S (optionT SetM)`. `None` means an exception for `stexcnd`, which
  supplies `raiseP`/`catchP`; it means divergence for `stdivnd`, which supplies
  `divergeD`, `mayDiverge`, and `orD` without its own `MonadExc` instance.
- [`stdivexcnd`](StDivExcNonDet.v) uses two option layers. Its raw outcomes
  are `Some (Some (a, s'))` for return, `Some None` for exception, and
  outer `None` for divergence. `spinP` selects the divergent outcome.
- [`stdivitree`](StDivITree.v) uses `stateT S (optionT (itree void1))`.
  Returning `None` is an exception; divergence belongs to the underlying
  ITree behavior. Its base equality is `eutt eq`.
- [`divnd`](DivNonDet.v) removes state; [`rddivnd`](RdDivNonDet.v) adds
  `readerT R` to it. Reader outcomes contain no final environment, unlike
  state outcomes, which contain the final state.
- [`nonEmptyOutcomes` / `stdivndNE`](StDivNonDet.v) require an outcome at
  every initial state. The pure and reader modules have corresponding fragments.

## Dependency boundaries

- Concrete stacks reuse ExtLib transformers and ITree laws. `StExcNonDet.v`
  supplies the shared `SetM` base used by the other nondeterministic models.
- [TransformerLaws.v](TransformerLaws.v) proves `Eq1`-generic option, state,
  and reader transformer laws from base `MonadLawsE` assumptions. It names
  no concrete computation monad, so [base specifications](../BaseSpecMonads/CONTEXT.md)
  can import it without depending on a concrete computation.
- Observation-specific readings and triples belong in
  [SP](../EffectObservations/SP/CONTEXT.md) or [WP](../EffectObservations/WP/CONTEXT.md).
  Raw outcome lemmas can also live here: `DivNonDet.outcomes_bind` is reused
  downstream without choosing an SP or WP reading.

## Semantic traps

- The exception/divergence distinction for the single-option models is
  semantic, not enforced by distinct raw carriers. Qualify repeated operation
  names when several computation modules are imported.
- An empty outcome set is blocking: it is neither a return nor the explicit
  divergence token. `stdivndNE` excludes it; it does not require termination.
- State-over-option failure has no final state in its outcome.
- [`denote`](StDivExcNonDet.v) interprets `freeprog` using ITree handlers,
  `Leaf`, and `any_infinite`. ITree's state handler returns `(state, result)`;
  the ExtLib stack stores `(result, state)`, so the definition swaps them.

## Reading order

Start with `SetM` and the single-option semantics, then the double-option or
ITree model needed by the client. Read non-empty fragments before the
[`WSt` observations](../EffectObservations/WP/StDivNonDet_WSt.v).
Read `TransformerLaws.v` when following a law instance through a stack;
use the [README](../README.md#2-computation-monads) for the complete effect table.
