# WP observations context

Parent: [effect observations](../CONTEXT.md).
Related: [computation monads](../../ComputationMonads/CONTEXT.md),
[base specifications](../../BaseSpecMonads/CONTEXT.md), and [SP observations](../SP/CONTEXT.md).
Details: [README, WP observations](../../README.md#wp-side--effectobservationswp).

## Purpose and scope

These modules define weakest-precondition observations into `WStExc` or `WSt`,
their local laws, and supported triples. The parent taxonomy modules assemble
cross-observation inclusions and the WP/SP comparisons.

## Established terms and definitions

- [`WPure`](../../BaseSpecMonads/WPureMonad.v) bundles postcondition-monotone
  transformers. `WStExc` postconditions range over `option (A * S)`;
  `WSt` postconditions range over `A * S`.
- In [StDivExcNonDet_WStExc.v](StDivExcNonDet_WStExc.v), `obsDWP` requires
  every outcome to terminate and satisfy `post`; `obsDWLP` requires this
  only of terminating outcomes. `obsAWP` requires some terminating outcome
  satisfying `post`; `obsAWLP` also accepts possible divergence.
- `obs*_mono` supplies the proof used by `mkWPure`. Public `obs*_run` or
  `obs*_unfold` lemmas expose readings without unpacking dependent proofs.
- [`tripleWP`](StDivExcNonDet_WStExc.v) takes an observation explicitly.
  `SubsetOf` means `pre s -> obs prog s post`; `SupersetOf` reverses it.
  These compare input predicates, unlike SP triples' output predicates.

## Dependency boundaries

- Each definition module connects a computation model to
  [WPureMonad.v](../../BaseSpecMonads/WPureMonad.v); the target itself has no
  concrete computation dependency. Its transformer laws come from generic
  [TransformerLaws.v](../../ComputationMonads/TransformerLaws.v).
- The double-option return/bind proofs use
  [StDivExcNonDet.outcomes_ret / outcomes_bind](../../ComputationMonads/StDivExcNonDet.v)
  directly. `TermSliceObsWP.outcomes_bind` in
  [StDivNonDet_WSt.v](StDivNonDet_WSt.v) is a non-empty-carrier adapter for
  [StExcNonDet.outcomes_bind](../../ComputationMonads/StExcNonDet.v): projecting
  `bindNE` through `getNE` gives the underlying `bindD` definitionally.
- [Double-option comparisons](../Taxonomy_StDivExcNonDet_StExc.v) and
  [state-only comparisons](../Taxonomy_StDivNonDet_St.v) consume these readings.
  Definition modules also retain local collapse lemmas and examples.

## Independent state and result types

The four return laws in [StDivExcNonDet_WStExc.v](StDivExcNonDet_WStExc.v) —
`obsDWP_ret`, `obsDWLP_ret`, `obsAWP_ret`, and `obsAWLP_ret` — compare the
observation of `ret a : stdivexcnd S A` with `WPureMonad.retP S a`.
The correction from `retP A a` to `retP S a` removes the earlier restriction
that state and result have the same type. The laws take `s0 : S` and
`post : option (A * S) -> Prop`.

The [audit](../../../Checks/Assumptions.v) instantiates each law with `bool`
state and `0 : nat`. These `Check` commands verify the type instantiations,
not program behavior.

## Semantic traps

- In `WStExc`, `post None` describes an exception. For the double-option
  source this is raw `Some None`; raw outer `None` is divergence and is
  handled by the choice of total or liberal observation.
- [StExcNonDet_WStExc.v](StExcNonDet_WStExc.v) defines `obsDWP` and `obsAWP`
  only. Its source offers exceptions without a separate divergence outcome,
  so it supplies no distinct liberal readings.
- [StDivNonDet_WSt.v](StDivNonDet_WSt.v), in `TermSliceObsWP`, takes
  `stdivndNE`. Divergence is visible to the observation but not to its
  postcondition. Non-emptiness supports `obsDWP_strict`, `obsAWLP_top`, and
  taxonomy inclusions; postcondition monotonicity alone does not require it.
- [StDivITree_WStExc.v](StDivITree_WStExc.v) proves `obsWPCollapse` and
  `obsWLPCollapse` from determinism. Its classical convergence/divergence
  argument uses `ITree.Extra.Dijkstra.PureITreeBasics`. These are different
  from total/liberal collapse under a no-divergence hypothesis.
- `ordWSt` / `ordWStExc` use forward implication. The base `WP_le` uses
  reverse implication; it is not the convention lifted by these stack orders.

## Reading order

Read `WPureMonad.v`, then the source's outcome encoding and computation-owned
raw laws. Read `stdivndNE` and its `getNE` adapter for the non-empty source.
Use the observation's monotonicity and unfolding lemmas before return/bind
proofs or triples. Use the deterministic file for angelic/demonic collapse,
the non-empty state-only file for divergence absent from postconditions, and the
[parent comparison layer](../CONTEXT.md) for the resulting taxonomy.
