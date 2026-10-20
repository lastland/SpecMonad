# Readings context

Parent: [Taxonomy context](../CONTEXT.md).
Inputs: [computation monads](../ComputationMonads/CONTEXT.md) and
[base specification monads](../BaseSpecMonads/CONTEXT.md).
Morphism interface: [MonadMorphism.v](../../Classes/MonadMorphism.v).

## Purpose and scope

This directory treats every predicate-transformer monad as a READING of one
relation specification monad. An observation of a computation factors as
the computation's relation followed by a reading. Monad structure belongs to
the relation. The order, the healthiness, and which triples an index carves
out belong to the reading. [PureReadings.v](PureReadings.v) covers the
state-free case, with `Rel = PredM.Pred`. [StateReadings.v](StateReadings.v)
covers state, with `RelSt S = stateT S Rel`.

## Vocabulary and contracts

- A **reading** is a `MonadMorphism` out of the relation monad (`rho*`).
  An observation that needs more than the relation reads the computation
  directly (`obsDWP`, `obsAWLP`).
- `slice` keeps a `divnd` computation's terminating outcomes. AWP, DWLP and
  all four SP readings factor through it. DWP and AWLP do not: no monad
  morphism from `Rel` lands in their healthy monads (`no_reading_Rel_DWP`,
  `no_reading_Rel_AWLP`).
- The WP targets `AWP`, `DWLP`, `DWP` and `AWLP` are subset monads of
  `WPure` carved out by healthiness (`WH`). The healthiness conditions are
  strict or terminating, and disjunctive or conjunctive over nonempty
  families. The SP targets are the arrow monads `ASP`, `DSLP`, `DSP` and
  `ASLP` at input `unit`.
- **Carved out** (`carvedBy`) means some index `w` has
  `T x <-> ρ x <= w`, so the Dijkstra monad at `w` contains exactly the
  computations the triple accepts. The opposite direction is the same
  notion for the flipped order.
- With state, a WP reading reads the outcomes of one start state, so it is
  the pure reading lifted by `liftSt`. `MonadMorphism_stateT` and
  `OrderedMonad_stateT` transfer the pure results. An SP reading reads the
  predecessors of one outcome, so each SP morphism is proved directly.

## Semantic cautions

- `Rel` shares its carrier with `SetM`, whose `Eq1` is Leibniz equality.
  Statements that depend on `Rel`'s pointwise-iff `Eq1` name its instances
  explicitly.
- In the state-free case DSP coincides with ASP and ASLP with DSLP, so both
  are ordered monads under their own orders. The stateful refutations in
  [DSPMonad.v](../BaseSpecMonads/DSPMonad.v) need a second start state.
  With one, the DSP order also bounds predecessor sets from above
  (`rhoDSPSt_order`), and relational `bind` does not preserve it
  (`dspSt_order_not_bind_mono`).
- An incorrectness triple is carved out by ASP when its precondition is one
  start state and not when it has two (`incorrectSt_carved_one`,
  `incorrectSt_not_carved_two`).
- The DSP and ASLP results use `classic` through the relation recovery in
  `BaseSpecMonads`. The WP, ASP and DSLP results use no axioms.
- `wp_sub_carved` and `wp_sup_carved` use indices of `WPure` outside the
  healthy monads. Within a healthy monad, which is isomorphic to `Rel`,
  only single-inclusion classes are carved out (`carved_iso`,
  `angelic_not_carved_AWP`).

## Reading order

Read the relation monad and `slice`, then the healthy WP monads and their
readings, then the DSP/ASLP collapse, and finish with the carving results.
Then read `StateReadings.v` in the same order. Its WP half is short because
it only lifts; its SP orders and examples show what a second start state
changes.
