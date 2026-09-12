# Effect observations context

Parent: [Taxonomy context](../CONTEXT.md).
Details: [observations](../README.md#5-observations) and
[their comparisons](../README.md#6-comparing-observations--taxonomy_v).

## Purpose and scope

This layer connects concrete computations to independently defined
specifications. `SP/` and `WP/` define observations, their local laws, triples,
and examples. The root `Taxonomy_*.v` modules compare observations and assemble
the taxonomy of triples.

## Established terms and source anchors

- An **observation** chooses a reading of a computation's outcomes in a
  target specification carrier. File names identify the source and target;
  see [`StDivNonDet_SPStExc.v`](SP/StDivNonDet_SPStExc.v).
- `outcomes_ret` and `outcomes_bind` expose concrete operational semantics.
  The `obs*_ret` / `obs*_bind` theorems establish preservation of the chosen
  specification operations, using those outcome laws or shared normalization.
- A **terminating slice** keeps returning outcomes and projects away
  divergence. It includes exceptions when the retained outcome is an option;
  see [`StDivExcNonDet_SPStExc.v`](SP/StDivExcNonDet_SPStExc.v).
- A **full-outcome observation** of `stdivnd` retains its divergence token:
  `FullOutcomeObs` indexes its SP target by `option (A * S)`.

## Dependency boundaries

- Definition modules depend on their [computation](../ComputationMonads/CONTEXT.md)
  and [base-monad](../BaseSpecMonads/CONTEXT.md) or [arrow](../Arrows/CONTEXT.md)
  target. The specification side has no concrete computation dependency;
  [TransformerLaws](../ComputationMonads/TransformerLaws.v) remains generic.
- Shared helpers are explicit: [arrow judgments](SP/SPostArrObservation.v)
  operate on observed specifications, [raw single-option laws](SP/RawStOpt_SPostArr.v)
  handle concrete outcomes, and the reader observation reuses the pure one.
- [Taxonomy_StDivExcNonDet_StExc.v](Taxonomy_StDivExcNonDet_StExc.v) combines
  WP/SP comparisons. Its `dwlp_slice`, `awp_slice`, `dwlp_asp`, and `awp_dslp`
  relate WP and SP triples through the same terminating relation.
- [Full-outcome comparisons](Taxonomy_StDivNonDet_StExc.v) and
  [state-only comparisons](Taxonomy_StDivNonDet_St.v) keep their outcome
  indexing explicit. Shared programs come from [ExampleProgramDefs.v](../ExampleProgramDefs.v).

## Semantic traps

- Fix both the source and the target indexing before interpreting `None`.
  The same SP carrier can expose divergence for `stdivnd` but only exceptions
  for the terminating slice of `stdivexcnd`.
- Defining versus comparing is the architectural split. Local collapse and
  simplification lemmas also occur in definition modules; do not infer their
  absence from that split.
- Nonempty outcome hypotheses matter for demonic-to-angelic WP inclusions.
  The `WSt` source packages this as `stdivndNE`; unrestricted sets can be empty.
- Repeated `obs*` names require source/module qualification. Mixed taxonomy
  files import SP modules after WP sections to avoid shadowing WP names.
- Angelic WP coverage quantifies over inputs before choosing outputs;
  ASP `Under` coverage quantifies over asserted outputs before choosing inputs.
  `WithdrawExample` in the double-option taxonomy demonstrates the difference.

## Reading order

Choose [SP](SP/CONTEXT.md) or [WP](WP/CONTEXT.md), inspect the observation's
source outcomes and target carrier, then read its laws and triples. Follow the
matching root taxonomy module for inclusions, contrapositive pairs, and
cross-reading examples; the [README](../README.md#5-observations) has the full matrix.
