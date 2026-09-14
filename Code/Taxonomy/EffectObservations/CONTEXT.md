# Effect observations context

Parent: [Taxonomy](../CONTEXT.md). Read [computation outcomes](../ComputationMonads/CONTEXT.md)
and [target specifications](../BaseSpecMonads/CONTEXT.md) first.

[SP](SP/CONTEXT.md) and [WP](WP/CONTEXT.md) map computations to specifications;
the parent files compare readings, inclusions, contrapositive pairs, and triples.
Arrow-derived SP clients coexist with the earlier OldMonads-targeted clients.
Return/bind preservation refers to actual selected dictionaries, not just types.

Taxonomy_StDivExcNonDet_StExc compares the terminating double-option slice,
including exceptions. Taxonomy_StDivNonDet_StExc retains full single-option
outcomes. Taxonomy_StDivNonDet_St compares terminating SP slices with WP over
the nonempty computation fragment. Preserve nonemptiness assumptions;
empty outcome sets are not divergent executions.

SP Over means observed implies asserted; Under reverses it. WP local triple
constructors/orders may reverse that direction and have different argument
positions. In-monad SP targets can require a fixed-precondition order and side
conditions. Always inspect definitions before transporting a theorem.

The double-option wp/sp equivalences identify specified triples, not all
carrier bundles. WithdrawExample contrasts angelic WP coverage with ASP bug
presence. Shared programs are in ExampleProgramDefs. Read observation bodies
and outcome cases before laws, comparisons, and examples; qualify repeated
obs/pre/post names when mixing files.

- An **observation** chooses a reading of a computation's outcomes in a
  target specification carrier. File names identify the source and target;
  see [`StDivNonDet_SPStExc.v`](SP/StDivNonDet_SPStExc.v).
- Computation-owned `outcomes_ret` and `outcomes_bind` expose raw operational
  semantics. The `obs*_ret` / `obs*_bind` theorems establish preservation of
  the chosen specification operations, using those laws or derived adapters
  together with specification-side normalization.
- A **terminating slice** keeps returning outcomes and projects away
  divergence. It includes exceptions when the retained outcome is an option;
  see [`StDivExcNonDet_SPStExc.v`](SP/StDivExcNonDet_SPStExc.v).
- A **full-outcome observation** of `stdivnd` retains its divergence token:
  `FullOutcomeObs` indexes its SP target by `option (A * S)`.

## Dependency boundaries

- Definition modules depend on their [computation](../ComputationMonads/CONTEXT.md)
  and [base-monad](../BaseSpecMonads/CONTEXT.md) or [arrow](../Arrows/CONTEXT.md)
  target. Check the chosen target's actual imports for concrete dependencies;
  [TransformerLaws](../ComputationMonads/TransformerLaws.v) itself remains generic.
- The [raw outcome-law interface](../ComputationMonads/CONTEXT.md#raw-outcome-law-interface)
  belongs to computation modules. SP slice facts and non-empty WP statements
  derive from it; they do not supply independent raw normalization proofs.
- [Shared arrow judgments](SP/SPostArrObservation.v) operate on observed
  specifications. The reader observation reuses the pure observation.
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

Read the source computation's outcome encoding and raw laws, then choose an
[SP](SP/CONTEXT.md) or [WP](WP/CONTEXT.md) target. Inspect any slice or non-empty
adapter before the observation's preservation laws and triples. Follow the
matching root taxonomy module for comparisons and cross-reading examples;
the [README](../README.md#5-observations) has the full matrix.
