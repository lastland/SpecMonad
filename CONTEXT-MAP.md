# Global context map

This repository explores the connection between incorrectness logic and
Dijkstra/specification monads. Read the [project README](README.md) for goals
and status, [CLAUDE.md](CLAUDE.md) for development conventions, and the
[Taxonomy README](Code/Taxonomy/README.md) for detailed semantics.

## How to use this map

Start with the [Code context](Code/CONTEXT.md), then read the parent and local
contexts relevant to the task. Follow cross-context links when the work spans
areas. These contexts describe directory roles and established vocabulary;
linked source definitions determine exact types and theorem statements.
[Domain-document rules](docs/agents/domain.md) explain maintenance and ADR use.

## Architectural relationships

- **Common** supplies shared specification-monad interfaces and effect
  constructions used by the earlier effect-specific developments.
- **Classes** supplies generic arrow contracts, transformers, and arrow-derived
  monads. **Taxonomy/Arrows** instantiates those contracts with specification
  carriers.
- **Taxonomy/ComputationMonads** supplies computation semantics;
  **Taxonomy/BaseSpecMonads** supplies unary specification semantics.
  Specifications are independent of concrete computation monads. The generic
  `TransformerLaws.v` is an infrastructure dependency despite its location in
  `ComputationMonads/`.
- **EffectObservations/SP** and **EffectObservations/WP** connect computations
  to specifications. Their parent directory compares the observations.
- **Tests**, **Examples**, and **Checks** serve different purposes: instance/law
  regression, semantic clients, and reporting selected theorem assumptions.

## Active source contexts

| Directory context | Purpose |
|---|---|
| [Code](Code/CONTEXT.md) | Coq namespace, build boundaries, and shared distinctions |
| [Common](Code/Common/CONTEXT.md) | Specification-monad interfaces and effect constructions |
| [Classes](Code/Classes/CONTEXT.md) | Generic arrow contracts and constructions |
| [Classes/OptionArrowT](Code/Classes/OptionArrowT/CONTEXT.md) | Option-arrow transformer and algebraic laws |
| [Classes/StateArrowT](Code/Classes/StateArrowT/CONTEXT.md) | State-arrow transformer and algebraic laws |
| [Classes/Tests](Code/Classes/Tests/CONTEXT.md) | Generic arrow-to-monad regression checks |
| [Identity](Code/Identity/CONTEXT.md) | Pure correctness and incorrectness developments |
| [Reader](Code/Reader/CONTEXT.md) | Reader specifications and observations |
| [ST](Code/ST/CONTEXT.md) | State predicate specifications and guarded variants |
| [STEx](Code/STEx/CONTEXT.md) | State/exception specifications and examples |
| [Checks](Code/Checks/CONTEXT.md) | Opt-in theorem-assumption reporting |
| [Taxonomy](Code/Taxonomy/CONTEXT.md) | Computation/specification separation and observation taxonomy |
| [Taxonomy/ComputationMonads](Code/Taxonomy/ComputationMonads/CONTEXT.md) | Effect stacks and their outcome semantics |
| [Taxonomy/BaseSpecMonads](Code/Taxonomy/BaseSpecMonads/CONTEXT.md) | Unary SP/WP specifications, well-formedness, and orders |
| [Taxonomy/Arrows](Code/Taxonomy/Arrows/CONTEXT.md) | Binary specifications and SP presentation equivalence |
| [Taxonomy/Arrows/Examples](Code/Taxonomy/Arrows/Examples/CONTEXT.md) | Checked SP-arrow clients |
| [Taxonomy/Arrows/Tests](Code/Taxonomy/Arrows/Tests/CONTEXT.md) | Concrete monad and transformer instances |
| [Taxonomy/EffectObservations](Code/Taxonomy/EffectObservations/CONTEXT.md) | Cross-observation comparisons and triples |
| [Taxonomy/EffectObservations/SP](Code/Taxonomy/EffectObservations/SP/CONTEXT.md) | SP observations and shared arrow judgments |
| [Taxonomy/EffectObservations/WP](Code/Taxonomy/EffectObservations/WP/CONTEXT.md) | Angelic/demonic, total/liberal WP observations |
| [Taxonomy/OldSP](Code/Taxonomy/OldSP/CONTEXT.md) | Earlier reading-based SP results, partly still built |

## Reading by task

- **Understand a program's effects:** computation context → relevant SP/WP
  context → comparison layer. Check what `None` means at each outcome layer.
- **Change an SP representation:** arrows context → well-formedness properties
  and equivalence → examples and concrete tests.
- **Change a generic law or transformer:** Classes context → transformer
  context → generic tests → concrete Taxonomy tests.
- **Understand a verification judgment:** read the local definition and order;
  similarly named judgments can reverse implication direction.
- **Inspect proof assumptions:** Checks context → current audit source and
  output. The map does not certify axiom-freedom.

## Historical, research, and supporting areas

| Area | Status and reading guidance |
|---|---|
| [Taxonomy/deprecated](Code/Taxonomy/deprecated/) | Earlier iterations excluded from `_CoqProject`; omit from normal symbol searches |
| [Backup](Code/Backup/) | Historical sources outside the normal build |
| [ITreeExamples](Code/ITreeExamples/README.md) | Copied upstream ITree examples; provenance is recorded in their README |
| [MeetingNotes](Code/Taxonomy/MeetingNotes/) and [paper notes](POPL-Paper-Notes.md) | Historical research discussion, not adopted ADRs or current API authority |
| [F* experiment](fstar/) | Separate experiment outside the Coq build |
| `Papers/` | Local reference PDFs; availability is checkout-specific |
| [CI workflow](.github/workflows/SpecMonad.yml) | Coq CI configuration |
| Agent setup | [Tracker](docs/agents/issue-tracker.md), [labels](docs/agents/triage-labels.md), and [domain-document consumer rules](docs/agents/domain.md) |

Coverage follows the active Coq sources in [the build manifest](Code/_CoqProject)
plus the opt-in audit in [Makefile.local](Code/Makefile.local), including source
parent directories. Generated output, local agent configuration, `.scratch/`,
and separate worktrees do not receive directory contexts.
