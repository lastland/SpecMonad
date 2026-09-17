# Global context map

This repository studies incorrectness logic through Dijkstra/specification
monads. See the [README](README.md) for project goals and
[CLAUDE.md](CLAUDE.md) for development conventions.

## Reading order

Start with [Code](Code/CONTEXT.md), then read the parent and local contexts
for the area you are changing. Follow their source links for exact types,
orders, and theorem statements. The [domain-document rules](docs/agents/domain.md)
describe how skills consume and maintain these documents.

## Architectural relationships

- **Common** supplies specification-monad interfaces and effect constructions
  used by the earlier Identity, Reader, ST, and STEx developments.
- **Classes** supplies generic arrow contracts and option/state transformers.
  **Taxonomy/Arrows** defines concrete binary specification carriers.
- **Taxonomy/ComputationMonads** defines effectful computations;
  **Taxonomy/BaseSpecMonads** defines unary specifications. The generic
  `TransformerLaws.v` also supports specification stacks despite its location
  in the computation directory.
- **EffectObservations/SP** and **EffectObservations/WP** map computations
  into specifications. Their parent directory compares observations and triples.
- **OldSP** contains an earlier presentation with some files still in the build.

## Active source contexts

Coverage follows source files listed in [Code/_CoqProject](Code/_CoqProject),
including their parent directories.

| Context | Role |
|---|---|
| [Code](Code/CONTEXT.md) | Build boundary and shared semantic distinctions |
| [Common](Code/Common/CONTEXT.md) | Shared specification-monad interfaces |
| [Classes](Code/Classes/CONTEXT.md) | Generic arrow contracts |
| [OptionArrowT](Code/Classes/OptionArrowT/CONTEXT.md) | Option-arrow construction and laws |
| [StateArrowT](Code/Classes/StateArrowT/CONTEXT.md) | State-arrow construction and laws |
| [Identity](Code/Identity/CONTEXT.md) | Pure correctness and incorrectness |
| [Reader](Code/Reader/CONTEXT.md) | Reader specifications |
| [ST](Code/ST/CONTEXT.md) | State predicates and guarded specifications |
| [STEx](Code/STEx/CONTEXT.md) | State and exception specifications |
| [Taxonomy](Code/Taxonomy/CONTEXT.md) | Computation/specification relationships |
| [ComputationMonads](Code/Taxonomy/ComputationMonads/CONTEXT.md) | Effect stacks and outcome meanings |
| [BaseSpecMonads](Code/Taxonomy/BaseSpecMonads/CONTEXT.md) | Unary specifications, healthiness, and orders |
| [Arrows](Code/Taxonomy/Arrows/CONTEXT.md) | Binary specification carriers |
| [EffectObservations](Code/Taxonomy/EffectObservations/CONTEXT.md) | Observation comparisons and triples |
| [SP observations](Code/Taxonomy/EffectObservations/SP/CONTEXT.md) | Strongest-postcondition observations |
| [WP observations](Code/Taxonomy/EffectObservations/WP/CONTEXT.md) | Weakest-precondition observations |
| [OldSP](Code/Taxonomy/OldSP/CONTEXT.md) | Earlier SP presentation, partly built |

## Other areas

- `Code/Backup/`, `Code/Taxonomy/deprecated/`, and `Code/ITreeExamples/` are
  outside the current build manifest. Consult them deliberately rather than
  treating them as the current API.
- `Code/Taxonomy/MeetingNotes/` and [paper notes](POPL-Paper-Notes.md) record
  research discussion, not adopted architectural decisions.
- `fstar/` is a separate experiment outside the Coq build.
- [CI](.github/workflows/SpecMonad.yml) and [agent configuration](docs/agents/domain.md)
  support the development; they are not source contexts.

Generated files and separate worktrees are outside this map. When the build
manifest changes, update its context coverage as well.
