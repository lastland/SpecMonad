# Computation monads context

Parent: [Taxonomy](../CONTEXT.md). Consumers: [Triples](../Triples/CONTEXT.md)
and [DijkstraMonads](../DijkstraMonads/CONTEXT.md).

These modules own computations and outcome relations, not specification
well-formedness or readings. TransformerLaws is generic ExtLib infrastructure
for option/state stacks and is also used by specifications. Avoid
duplicating library laws or computation-owned raw outcome laws in clients.

[DivNonDetNE.v](DivNonDetNE.v) is the one file of computation monads. It
builds the base monad in three steps and then applies two transformer stacks
to it:

- `SetM A := A -> Prop` represents a set of outcomes; return is a singleton
  and bind existentially composes sets.
- `divnd` is `optionT SetM`, with `None` divergence and `divergeD`; it has no
  `MonadExc` instance. Its outcome law `outcomes_bind` is a constructive
  pointwise `<->` statement, not an equality of computations.
- `divndNE` is the fragment of `divnd` with at least one outcome, with
  `retNE`, `bindNE`, `orNE`, `divergeNE`. It is the base monad everything
  else uses.
- `stdivndNE S` is `stateT S divndNE` and `stdivexcndNE S` is
  `stateT S (optionT divndNE)`, with `orSt`, `divergeSt`, `orStExc`,
  `divergeStExc`, `raiseStExc`, `pickStExc` and the outcome lemmas `outSt_*` /
  `outStExc_*`. With state and exceptions, outer `None` is divergence,
  `Some None` an exception, and `Some (Some (a, s))` a normal return.

## Dependency boundaries

- The two stacks are ExtLib's `stateT` and `optionT` applied to `divndNE`;
  no stack is defined by hand.
- [TransformerLaws.v](TransformerLaws.v) proves `Eq1`-generic option and state
  transformer laws from base `MonadLawsE` assumptions. It names
  no concrete computation monad, so [base specifications](../BaseSpecMonads/CONTEXT.md)
  can import it without depending on a concrete computation.
  Its `ord_optionT` and `bind_optionT_mono` separately lift an explicit
  reflexive order and simultaneous bind monotonicity through `optionT`.
  `optionT_map` and `stateT_map` lift a map between monads;
  `MonadMorphism_optionT` / `_stateT` lift its morphism laws.

## Semantic traps

- An empty outcome set is blocking: it is neither a return nor the explicit
  divergence token. `divndNE` excludes it; it does not require termination.
- Bind runs the continuation only after a normal return and propagates failure
  tokens unchanged. An empty prefix therefore blocks, but an empty continuation
  does not erase a preceding exception or divergence.
- State-over-option failure has no final state in its outcome.
- `empty_prefix_blocks` and `diverge_survives_empty` in
  [DivNonDetNE.v](DivNonDetNE.v) check the blocking and absorbing points on
  `divnd`.

## Reading order

Read `DivNonDetNE.v` top to bottom: `SetM`, `divnd`, `divndNE`, the two
stacks. Read `TransformerLaws.v` when following a law instance or a lifted
morphism through a stack; use the [README](../README.md#2-computation-monads)
for the table of levels.
