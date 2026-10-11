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
- Computation owns effect outcomes (`divndNE` and its stacks). Relational owns
  relations, their four SP readings and `Pred`: proof infrastructure that SP
  builds on.
- WP and SP own the specification monads, their properties and orders. The
  SP arrows (`SPostArr.v`, `DSPASLPArr.v`) never import the SP monad files.
- PTMonadTaxonomy states implication, contrapositive and Galois connection on bare
  transformers and then as monadic relations between the monads.
- Triples defines monad morphisms out of `divndNE` and its stacks, lifts their
  triples, and proves the triple diagram at the state level and with
  exceptions. DijkstraMonads gives each morphism its Dijkstra monad and identifies
  triples with typings.
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
| [Computation](Computation.md) | §1, §5 | Outcomes and effect stacks |
| [Relational](Relational.md) | — | Relations, SP readings, `Pred` |
| [WP](WP.md) | §2, §3.6 | WP monads and variants |
| [SP](SP.md) | §3.1-3.5 | SP arrows and monads |
| [PTMonadTaxonomy](PTMonadTaxonomy.md) | §4 | Implication, contrapositive, Galois; Figure 1 |
| [Triples](Triples.md) | §5 | Morphisms out of `divndNE`, triples, diagram, examples, rewriting rules |
| [DijkstraMonads](DijkstraMonads.md) | §6 | Dijkstra monad of a monad morphism; triples as typings |
| [GaloisConnections](GaloisConnections.md) | §7 | DM4All monads and adjunctions |
| [Tests](Tests.md) | — | Generic regression, concrete instances, semantic clients |
| [Checks](Checks.md) | — | Assumption reporting, paper claims |

## Reading by task and other areas

For effects, read computation → Triples contexts. For a
representation change, read carrier → equivalence → examples/tests. For a
generic law, read Lib → transformer → generic/concrete tests. For a
judgment, check its outcome type, quantifiers, and order direction. For Dijkstra
typings, read carrier/order → Triples → DijkstraMonads. For a paper claim, start
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
