# Global context map

Read the [README](README.md) for project goals, [CLAUDE.md](CLAUDE.md) for
development conventions, and the [Taxonomy README](Code/Taxonomy/README.md)
for semantics. Start with [Code](Code/CONTEXT.md), then the parent and local
contexts for the task. Source declarations determine exact contracts.
See [domain-document rules](docs/agents/domain.md) for maintenance and ADR use.

## Architectural relationships

- Common supplies specification interfaces for the earlier effect examples.
- Classes supplies generic arrows, transformers, morphisms, and arrow monads.
  Taxonomy/Arrows supplies concrete binary specification carriers.
- ComputationMonads owns effect outcomes; BaseSpecMonads owns unary
  specifications, their properties, orders, and adjunctions. The generic
  `TransformerLaws.v` serves both despite its computation-directory location.
  Consult imports: directory ownership does not establish semantic independence.
- EffectObservations connects computations to specifications; its parent
  compares readings and triples. OldSP retains some built earlier results.
- Tests check instances/laws, Examples check semantic clients, and Checks
  reports selected theorem assumptions. The map does not certify axiom-freedom.

## Active source contexts

Coverage follows [the manifest](Code/_CoqProject), its parent directories,
and the opt-in assumption audit.

| Context | Role |
|---|---|
| [Code](Code/CONTEXT.md) | Namespace, build boundaries, shared distinctions |
| [Common](Code/Common/CONTEXT.md) | Earlier specification interfaces |
| [Classes](Code/Classes/CONTEXT.md) | Generic arrow contracts |
| [OptionArrowT](Code/Classes/OptionArrowT/CONTEXT.md) | Option-arrow operations and laws |
| [StateArrowT](Code/Classes/StateArrowT/CONTEXT.md) | State-arrow operations and laws |
| [Classes tests](Code/Classes/Tests/CONTEXT.md) | Generic monad regression |
| [Identity](Code/Identity/CONTEXT.md) | Pure correctness/incorrectness |
| [Reader](Code/Reader/CONTEXT.md) | Environment-indexed specifications |
| [ST](Code/ST/CONTEXT.md) | Ordinary and guarded state |
| [STEx](Code/STEx/CONTEXT.md) | State and exceptions |
| [Checks](Code/Checks/CONTEXT.md) | Opt-in assumption reporting |
| [Taxonomy](Code/Taxonomy/CONTEXT.md) | Computation/specification taxonomy |
| [ComputationMonads](Code/Taxonomy/ComputationMonads/CONTEXT.md) | Outcomes and effect stacks |
| [BaseSpecMonads](Code/Taxonomy/BaseSpecMonads/CONTEXT.md) | Unary specifications and orders |
| [Arrows](Code/Taxonomy/Arrows/CONTEXT.md) | Binary carriers and equivalences |
| [Arrow examples](Code/Taxonomy/Arrows/Examples/CONTEXT.md) | Semantic clients |
| [Arrow tests](Code/Taxonomy/Arrows/Tests/CONTEXT.md) | Concrete instances |
| [EffectObservations](Code/Taxonomy/EffectObservations/CONTEXT.md) | Reading/triple comparisons |
| [SP observations](Code/Taxonomy/EffectObservations/SP/CONTEXT.md) | SP readings and judgments |
| [WP observations](Code/Taxonomy/EffectObservations/WP/CONTEXT.md) | Four WP readings |
| [OldSP](Code/Taxonomy/OldSP/CONTEXT.md) | Earlier presentation, partly built |

## Reading by task and other areas

For effects, read computation → observation → comparison contexts. For a
representation change, read carrier → equivalence → examples/tests. For a
generic law, read Classes → transformer → generic/concrete tests. For a
judgment, check its outcome type, quantifiers, and order direction.

`Taxonomy/deprecated/`, `Backup/`, and `ITreeExamples/` are outside the normal
manifest. Consult them deliberately; copied ITree provenance is in its README.
MeetingNotes and paper notes are research discussion, not adopted ADRs.
`fstar/` is separate; local `Papers/` availability is checkout-specific.
See [CI](.github/workflows/SpecMonad.yml), [tracker](docs/agents/issue-tracker.md),
and [labels](docs/agents/triage-labels.md) for supporting workflows.
Generated output, local agent configuration, and separate worktrees are outside
this map. Update context coverage when the manifest changes.
