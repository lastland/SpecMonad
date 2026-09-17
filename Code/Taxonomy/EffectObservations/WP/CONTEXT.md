# WP observations context (main)

Parent: [effect observations](../CONTEXT.md).
Target definitions: [WPureMonad.v](../../BaseSpecMonads/WPureMonad.v).
Related: [SP observations](../SP/CONTEXT.md).

## Purpose and scope

These files interpret computations as weakest-precondition specifications.
Each observation packages a monotone transformer using `mkWPure` and an
`obs*_mono` proof. The four source files have different theorem coverage;
their common naming does not imply a uniform interface.

## Source and target map

| Source file | Observation source and target | Main contents |
|---|---|---|
| [StDivITree_WStExc.v](StDivITree_WStExc.v) | `stdivitree` to `WStExc` | Four readings, deterministic collapse, `tripleWP`, examples. |
| [StExcNonDet_WStExc.v](StExcNonDet_WStExc.v) | `stexcnd` to `WStExc` | `obsDWP` / `obsAWP` and examples; no separate liberal readings. |
| [StDivExcNonDet_WStExc.v](StDivExcNonDet_WStExc.v) | `stdivexcnd` to `WStExc` | Four readings, return/bind laws, triples and refinement forms, examples. |
| [StDivNonDet_WSt.v](StDivNonDet_WSt.v) | `stdivndNE` to `WSt` | `TermSliceObsWP`: four readings, healthiness, return/bind laws, triples. |

The deterministic and exception-only files do not declare `obs*_ret` /
`obs*_bind` laws. The exception-only file also has no local triple interface.

## Four readings and divergence

For a fixed initial state, the divergence-aware readings mean:

| Observation | Requirement |
|---|---|
| `obsDWP` — demonic total | Every outcome terminates and satisfies the postcondition. |
| `obsDWLP` — demonic liberal | Every terminating outcome satisfies the postcondition. |
| `obsAWP` — angelic total | Some terminating outcome satisfies the postcondition. |
| `obsAWLP` — angelic liberal | Some terminating outcome satisfies it, or divergence is possible. |

Here termination can include an exception. `WStExc` postconditions range over
`option (A * S)`: `post None` constrains exceptions, not divergence.
For `stdivexcnd`, raw `Some None` reaches that exception outcome while raw
`None` denotes divergence. For `stdivitree`, convergence to `Ret None` is
the exception case. `WSt` postconditions range only over `A * S`.

`TermSliceObsWP` still inspects divergence even though its postcondition cannot
name it. Its source `stdivndNE` excludes empty outcome sets, not divergence;
`obsDWP_strict` and `obsAWLP_top` use that nonemptiness. On an unrestricted
empty outcome set, a universal requirement can hold vacuously.

`obsWPCollapse` / `obsWLPCollapse` in the ITree file equate angelic and demonic
readings under determinism. By contrast, `obsDPCollapse` / `obsAPCollapse` in
the divergence-aware nondeterministic files equate total and liberal readings
under an explicit no-divergence hypothesis. These are different collapses.

## Triple and order contracts

- The two nondeterministic files with triples use `approxKindWP`:
  `SubsetOf` means `pre` implies the computed WP, and `SupersetOf` reverses it.
  Their call order is `tripleWP obs prog pre kind post`.
- The ITree file instead uses `approximationKind`, with `Under` for the first
  implication and `Over` for the reverse, and takes `kind` before `pre`.
  Do not confuse these with SP's postcondition comparisons.
- `tripleWPspec` uses forward `ordWSt` / `ordWStExc`, not reverse `WP_le`.
  `pp2wp_subset` / `pp2wp_superset` supply the comparison targets;
  `tripleWPDefEq` retains a monotonicity hypothesis in its signature.

## Boundaries and reading order

Keep the generic WP carrier and stack laws in `WPureMonad.v`; cross-observation
inclusions, contrapositive pairs, and WP/SP equivalences live in the
[parent comparison files](../CONTEXT.md). Some current WP files also import
arrows and shared examples; do not assume an isolated WP-only import graph.
Read the observation body and outcome cases first. Use the ITree `obs*_run`
or state-only `obs*_unfold` lemmas before destructing through bundled proofs,
then follow the local laws, triples, examples, and comparison results.
