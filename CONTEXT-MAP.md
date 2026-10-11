# Global context map

Read the [README](README.md) for project goals, [CLAUDE.md](CLAUDE.md) for
development conventions, and the [Taxonomy README](Code/Taxonomy/README.md)
for semantics. Start with [Code](Code/CONTEXT.md), then the parent and local
contexts for the task. Source declarations determine exact contracts.
See [domain-document rules](docs/agents/domain.md) for maintenance and ADR use.

## Architectural relationships

- Classes supplies generic arrows, transformers, morphisms, and arrow monads.
  Taxonomy/Arrows supplies concrete binary specification carriers.
- ComputationMonads owns effect outcomes; BaseSpecMonads owns unary
  specifications, their properties, orders, and adjunctions. The generic
  `TransformerLaws.v` serves both despite its computation-directory location.
  Consult imports: directory ownership does not establish semantic independence.
- Triples defines monad morphisms out of the non-empty base `divndNE` and its
  transformer stacks, lifts their triples, and proves the taxonomy diagram at
  the state level and with exceptions. DijkstraMonads gives each of those
  morphisms its Dijkstra monad and identifies triples with typings.
- Tests check instances/laws, Examples check semantic clients, and Checks
  reports selected theorem assumptions. The map does not certify axiom-freedom.

## Active source contexts

Coverage follows [the manifest](Code/_CoqProject), its parent directories,
and the opt-in assumption audit.

| Context | Role |
|---|---|
| [Code](Code/CONTEXT.md) | Namespace, build boundaries, shared distinctions |
| [Classes](Code/Lib/CONTEXT.md) | Generic arrow contracts |
| [OptionArrowT](Code/Lib/Arrow/OptionArrowT/CONTEXT.md) | Option-arrow operations and laws |
| [StateArrowT](Code/Lib/Arrow/StateArrowT/CONTEXT.md) | State-arrow operations and laws |
| [Classes tests](Code/Tests/CONTEXT.md) | Generic monad regression |
| [Checks](Code/Checks/CONTEXT.md) | Opt-in assumption reporting |
| [Taxonomy](Code/Taxonomy/CONTEXT.md) | Computation/specification taxonomy |
| [ComputationMonads](Code/Computation/CONTEXT.md) | Outcomes and effect stacks |
| [BaseSpecMonads](Code/SP/CONTEXT.md) | Unary specifications and orders |
| [Arrows](Code/SP/CONTEXT-arrows.md) | Binary carriers and equivalences |
| [Arrow examples](Code/Tests/CONTEXT-examples.md) | Semantic clients |
| [Arrow tests](Code/Tests/CONTEXT-arrows.md) | Concrete instances |
| [DijkstraMonads](Code/Dijkstra/CONTEXT.md) | Dijkstra monad of a monad morphism; triples as typings |
| [Triples](Code/Triples/CONTEXT.md) | Lifted monad morphisms out of `divndNE`, triples, diagram, examples, rewriting rules |

## Reading by task and other areas

For effects, read computation → Triples contexts. For a
representation change, read carrier → equivalence → examples/tests. For a
generic law, read Classes → transformer → generic/concrete tests. For a
judgment, check its outcome type, quantifiers, and order direction. For Dijkstra
typings, read carrier/order → Triples → DijkstraMonads.

`Backup/` (with the former `Taxonomy/deprecated/`) and `ITreeExamples/` are outside the normal
manifest. Consult them deliberately; copied ITree provenance is in its README.
[Meeting notes](docs/meeting-notes) and paper notes are research discussion, not adopted ADRs.
`fstar/` is separate; local `Papers/` availability is checkout-specific.
See [CI](.github/workflows/SpecMonad.yml), [tracker](docs/agents/issue-tracker.md),
and [labels](docs/agents/triage-labels.md) for supporting workflows.
Generated output, local agent configuration, and separate worktrees are outside
this map. Update context coverage when the manifest changes.

The opt-in assumption audit runs through `make check` in the maintained
[Code/Makefile](Code/Makefile); generated Makefiles are not entry points.
