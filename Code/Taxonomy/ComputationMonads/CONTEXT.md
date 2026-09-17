# Computation monads context (main)

Parent: [Taxonomy context](../CONTEXT.md).
Consumers: [effect observations](../EffectObservations/CONTEXT.md).

## Purpose and scope

These modules define effectful computation models, their operations, and monad
law declarations. Choose a model by its outcome semantics, not just the number
of transformers: identical carriers can have different intended readings.

## Existing models

| Source | Type | Definition |
|---|---|---|
| [StDivITree.v](StDivITree.v) | `stdivitree S A` | `stateT S (optionT (itree void1)) A` |
| [StExcNonDet.v](StExcNonDet.v) | `stexcnd S A` | `stateT S (optionT SetM) A` |
| [StDivNonDet.v](StDivNonDet.v) | `stdivnd S A` | `stateT S (optionT SetM) A` |
| [StDivExcNonDet.v](StDivExcNonDet.v) | `stdivexcnd S A` | `stateT S (optionT (optionT SetM)) A` |
| [DivNonDet.v](DivNonDet.v) | `divnd A` | `optionT SetM A` |
| [RdDivNonDet.v](RdDivNonDet.v) | `rddivnd R A` | `readerT R divnd A` |

`SetM A = A -> Prop` is defined in `StExcNonDet.v`: return is a singleton,
bind existentially selects an intermediate value, and nondeterministic choice
unions outcome sets. `Eq1_SetM` is Leibniz equality, unlike the pointwise-iff
equality of the specification-side `PredM.Pred`.

## Outcome and operation contracts

- `stdivitree` is deterministic. After unwrapping state and option, convergence
  to `Ret None` is an exception; divergence belongs to the ITree behavior.
  Its base equivalence is `eutt eq`, lifted through the transformers.
- `stexcnd` reads `None` as an exception and supplies `raiseP` / `catchP`.
  `stdivnd` reads the same token as divergence and supplies `divergeD`,
  `mayDiverge`, and `orD`. Both thread state through normal `Some (a, s')` returns.
- The divergence modules deliberately declare no exception instance for that
  reading. This is an API convention, not a type-level separation:
  `stexcnd` and `stdivnd` are definitionally the same carrier.
- Unwrapped `stdivexcnd` has outcomes `Some (Some (a, s'))` for normal return,
  `Some None` for exception, and `None` for divergence. `spinP` supplies
  divergence; `pickP` chooses any result of its type. Neither exceptional nor
  divergent outcomes retain a final state.
- `rddivnd` supplies `askD` / `localD`, not mutable state. Its unwrapped
  outcomes have shape `R -> option A -> Prop`, without a final environment.

## Non-empty fragments and reusable laws

The raw nondeterministic carriers allow an empty outcome set. This is distinct
from the singleton divergence outcome. `stdivndNE`, `divndNE`, and `rddivndNE`
bundle `nonEmptyOutcomes`; `getNE` forgets the proof. Nonemptiness does **not**
mean termination: `divergeNE` belongs to each fragment. The
[state-only WP observations](../EffectObservations/WP/StDivNonDet_WSt.v) require
`stdivndNE` for their strictness/top-preservation and comparison results.

[TransformerLaws.v](TransformerLaws.v) owns generic `Eq1`, `Eq1Equivalence`,
and `MonadLawsE` instances for `optionT`, `stateT`, and `readerT`, and lifts
of `OrderedMonad` through each (`OrderedMonad_optionT` &c.). Reuse those
contracts; the file depends on no concrete computation or specification monad.
`DivNonDet.v` also gives pointwise `outcomes_bind`, `diverge_absorbing`, and
`mayDiverge_bind`. On main, the stateful `outcomes_bind` lemmas used by SP/WP
clients still live in the corresponding observation files.

## Reading guidance and boundaries

Read the chosen carrier, then the primitive operations and nonemptiness
requirements, then its observation's selected outcomes. Specification readings
and triple comparisons do not belong in this directory.
For the ITree interpretation, `StDivExcNonDet.v` defines `freeprog` and
`denote` using `run_state`, `throw_prefix`, `Leaf`, and `any_infinite`.
The normal-return case swaps ITree's `(state, result)` into ExtLib's
`(result, state)` order; do not infer additional preservation laws from the
existence of this definition.
