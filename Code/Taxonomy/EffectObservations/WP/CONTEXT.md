# WP observations context

Parent: [observations](../CONTEXT.md). Target: [WPureMonad](../../BaseSpecMonads/WPureMonad.v).

StDivITree_WStExc handles deterministic state/divergence/exception trees;
StExcNonDet_WStExc handles exception-only nondeterminism;
StDivExcNonDet_WStExc handles double-option outcomes; StDivNonDet_WSt handles
the nonempty state/divergence fragment. Theorem coverage differs across files:
similar observation names do not imply identical law packages.

The four readings at an initial state are demonic total (all outcomes
terminate and satisfy post), demonic liberal (all terminating outcomes satisfy
post), angelic total (some terminating outcome satisfies post), and angelic
liberal (some satisfies post or divergence is possible). Termination may
include exceptions. For double option, post None constrains exceptions, while
raw outer None is divergence. State-only WSt posts cannot mention exceptions.

Nonempty fragments exclude empty outcomes, not divergence. They justify
strictness/top preservation claims that fail vacuously on empty outcome sets.
Retain upstream excluded-miracle results. Deterministic WP collapse and
no-divergence total/liberal collapse are different theorems.

WP_le and ordWSt/ordWStExc are reverse-implication orders in the current
checkout; WP triple argument swaps preserve the intended meanings. Inspect
local approximation constructors and call order (the deterministic and
nondeterministic interfaces differ). tripleWPDefEq retains monotonicity.

Generic WP structure belongs to BaseSpecMonads. Comparisons, contrapositive
pairs, and WP/SP equivalences belong to the parent layer. Use run/unfold
lemmas before destructing bundles; read outcomes → observation → triple/order
→ comparison/examples. Shared programs live in ExampleProgramDefs.

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
- `ordWSt` / `ordWStExc` lift reverse `WP_le`; retain the corresponding
  WP triple argument swaps rather than changing orders independently.

## Reading order

Read `WPureMonad.v`, then the source's outcome encoding and computation-owned
raw laws. Read `stdivndNE` and its `getNE` adapter for the non-empty source.
Use the observation's monotonicity and unfolding lemmas before return/bind
proofs or triples. Use the deterministic file for angelic/demonic collapse,
the non-empty state-only file for divergence absent from postconditions, and the
[parent comparison layer](../CONTEXT.md) for the resulting taxonomy.
