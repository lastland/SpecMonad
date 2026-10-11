# Global context map

Read the [README](README.md) for project goals, [CLAUDE.md](CLAUDE.md) for
development conventions, [PAPER.md](PAPER.md) for the paper-to-code index,
and the [design notes](docs/design.md) for semantics. Start with [Code](Code/CONTEXT.md), then the parent and local
contexts for the task. Source declarations determine exact contracts.
See [domain-document rules](docs/agents/domain.md) for maintenance and ADR use.

## Architectural relationships

The directories under `Code/` follow the paper and form layers
([layers.txt](Code/scripts/layers.txt), checked by `make layers` and CI):

- Lib supplies generic arrows, transformers, morphisms, arrow monads, ordered
  monads and monadic relations; it names no specification carrier.
- Computation owns effect outcomes (`divndNE` and its stacks). Relational owns
  relations, their four SP readings and `Pred`: proof infrastructure that SP
  builds on.
- WP and SP own the specification monads, their properties and orders. The
  SP arrows (`SPostArr.v`, `DSPASLPArr.v`) never import the SP monad files.
- Taxonomy states implication, contrapositive and Galois connection on bare
  transformers and then as monadic relations between the monads.
- Triples defines monad morphisms out of `divndNE` and its stacks, lifts their
  triples, and proves the triple diagram at the state level and with
  exceptions. Dijkstra gives each morphism its Dijkstra monad and identifies
  triples with typings.
- GaloisConnections relates the DM4All specification monads.
- Tests check instances/laws and semantic clients; Checks reports selected
  theorem assumptions and checks the paper claims. The map does not certify
  axiom-freedom. Consult imports: directory ownership does not establish
  semantic independence.

## Active source contexts

Coverage follows [the manifest](Code/_CoqProject), its parent directories,
and the opt-in audits.

| Context | Paper | Role |
|---|---|---|
| [Code](Code/CONTEXT.md) | — | Namespace, build boundaries, shared distinctions |
| [Lib](Code/Lib/CONTEXT.md) | background | Generic arrow and monad contracts |
| [OptionArrowT](Code/Lib/Arrow/OptionArrowT/CONTEXT.md) | — | Option-arrow operations and laws |
| [StateArrowT](Code/Lib/Arrow/StateArrowT/CONTEXT.md) | — | State-arrow operations and laws |
| [Computation](Code/Computation/CONTEXT.md) | §1, §5 | Outcomes and effect stacks |
| [Relational](Code/Relational/CONTEXT.md) | — | Relations, SP readings, `Pred` |
| [WP](Code/WP/CONTEXT.md) | §2, §3.6 | WP monads and variants |
| [SP](Code/SP/CONTEXT.md) | §3.1-3.5 | SP arrows and monads |
| [Taxonomy](Code/Taxonomy/CONTEXT.md) | §4 | Implication, contrapositive, Galois; Figure 1 |
| [Triples](Code/Triples/CONTEXT.md) | §5 | Morphisms out of `divndNE`, triples, diagram, examples, rewriting rules |
| [Dijkstra](Code/Dijkstra/CONTEXT.md) | §6 | Dijkstra monad of a monad morphism; triples as typings |
| [GaloisConnections](Code/GaloisConnections/CONTEXT.md) | §7 | DM4All monads and adjunctions |
| [Tests](Code/Tests/CONTEXT.md) | — | Generic regression, concrete instances, semantic clients |
| [Checks](Code/Checks/CONTEXT.md) | — | Assumption reporting, paper claims |

## Reading by task and other areas

For effects, read computation → Triples contexts. For a
representation change, read carrier → equivalence → examples/tests. For a
generic law, read Lib → transformer → generic/concrete tests. For a
judgment, check its outcome type, quantifiers, and order direction. For Dijkstra
typings, read carrier/order → Triples → Dijkstra. For a paper claim, start
from [PAPER.md](PAPER.md).

`Backup/` (with the former `Taxonomy/deprecated/`) and `ITreeExamples/` are outside the normal
manifest. Consult them deliberately; copied ITree provenance is in its README.
[Meeting notes](docs/meeting-notes) and paper notes are research discussion, not adopted ADRs.
`fstar/` is separate; local `Papers/` availability is checkout-specific.
See [CI](.github/workflows/SpecMonad.yml), [tracker](docs/agents/issue-tracker.md),
and [labels](docs/agents/triage-labels.md) for supporting workflows.
Generated output, local agent configuration, and separate worktrees are outside
this map. Update context coverage when the manifest changes.

The opt-in audits run through `make check` in the maintained
[Code/Makefile](Code/Makefile); generated Makefiles are not entry points.
