# Global context map

Read the [README](../../../README.md) for project goals, [CLAUDE.md](../../../CLAUDE.md) for
development conventions, [PAPER.md](../../../PAPER.md) for the paper-to-code index,
and the [design notes](../../design.md) for semantics. Start with [Code](Code.md), then the parent and local
contexts for the task. Source declarations determine exact contracts.
See [domain-document rules](../domain.md) for maintenance and ADR use.

## Architectural relationships

The directories under `Code/` follow the paper and form layers
([layers.txt](../../../Code/scripts/layers.txt), checked by `make layers` and CI):

- Lib supplies generic arrows, transformers, morphisms, arrow monads, ordered
  monads and monadic relations; it names no specification carrier.
- `Verification/` groups everything that involves the computation monad, by
  setting: Base (`divndNE`), State and StateExc (its two lifts, siblings),
  and Generic (the same at every setting). Relational owns relations, their
  four SP readings and `Pred`: proof infrastructure that SP builds on.
- WP and SP own the specification monads, their properties and orders. The
  SP arrows (`SPostArr.v`, `DSPASLPArr.v`) never import the SP monad files.
- PTMonadTaxonomy states implication, contrapositive and Galois connection on bare
  transformers and then as monadic relations between the monads.
- In each setting: the computation monad, the eight readings as monad
  morphisms (the State and StateExc ones lifts of the Base ones), their
  triples, Verscht and Kaminski's diagram, the Dijkstra monads (which do not
  depend on triples), and which triples are typings.
- GaloisConnections relates the DM4All specification monads.
- Tests check instances/laws and semantic clients; Checks reports selected
  theorem assumptions and checks the paper claims. The map does not certify
  axiom-freedom. Consult imports: directory ownership does not establish
  semantic independence.

## Active source contexts

Coverage follows [the manifest](../../../Code/_CoqProject), its parent directories,
and the opt-in audits.

| Context | Paper | Role |
|---|---|---|
| [Code](Code.md) | — | Namespace, build boundaries, shared distinctions |
| [Lib](Lib.md) | background | Generic arrow and monad contracts |
| [OptionArrowT](Lib/Arrow/OptionArrowT.md) | — | Option-arrow operations and laws |
| [StateArrowT](Lib/Arrow/StateArrowT.md) | — | State-arrow operations and laws |
| [Relational](Relational.md) | — | Relations, SP readings, `Pred` |
| [WP](WP.md) | §2, §3.6 | WP monads and variants |
| [SP](SP.md) | §3.1-3.5 | SP arrows and monads |
| [PTMonadTaxonomy](PTMonadTaxonomy.md) | §4 | Implication, contrapositive, Galois; Figure 1 |
| [Verification](Verification.md) | §1, §5, §6 | The computation monad, morphisms, triples, Dijkstra monads; by setting |
| [Verification/Generic](Verification/Generic.md) | §5, §6 | General triple, Dijkstra construction, typings at any indices |
| [Verification/Base](Verification/Base.md) | §1, §5, §6 | `divndNE` and the eight base readings |
| [Verification/State](Verification/State.md) | §5, §6 | Lifts to state; diagram; O'Hearn's rules |
| [Verification/StateExc](Verification/StateExc.md) | §5, §6 | Lifts to state and exceptions; diagram; examples |
| [GaloisConnections](GaloisConnections.md) | §7 | DM4All monads and adjunctions |
| [Tests](Tests.md) | — | Generic regression, concrete instances, semantic clients |
| [Checks](Checks.md) | — | Assumption reporting, paper claims |

## Reading by task and other areas

For effects, read the Verification overview, then the setting. For a
representation change, read carrier → equivalence → examples/tests. For a
generic law, read Lib → transformer → generic/concrete tests. For a
judgment, check its outcome type, quantifiers, and order direction. For Dijkstra
typings, read carrier/order → Generic/DijkstraMonad.v → the setting's Dijkstra and Typings files. For a paper claim, start
from [PAPER.md](../../../PAPER.md).

`Backup/` (with the former `Taxonomy/deprecated/`) and `ITreeExamples/` are outside the normal
manifest. Consult them deliberately; copied ITree provenance is in its README.
[Meeting notes](../../meeting-notes) and paper notes are research discussion, not adopted ADRs.
`fstar/` is separate; local `Papers/` availability is checkout-specific.
See [CI](../../../.github/workflows/SpecMonad.yml), [tracker](../issue-tracker.md),
and [labels](../triage-labels.md) for supporting workflows.
Generated output, local agent configuration, and separate worktrees are outside
this map. Update context coverage when the manifest changes.

The opt-in audits run through `make check` in the maintained
[Code/Makefile](../../../Code/Makefile); generated Makefiles are not entry points.
