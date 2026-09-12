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
