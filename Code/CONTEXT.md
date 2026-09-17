# Code context

Parent: [global context map](../CONTEXT-MAP.md).
Conventions: [CLAUDE.md](../CLAUDE.md).

## Scope and authority

[_CoqProject](_CoqProject) identifies the active Coq sources and maps this
directory to the `Incorrectness` namespace. A file's presence on disk does
not establish that it belongs to the current build. Dependencies and build
instructions live in the [opam file](coq-spec-monad.opam) and
[project README](../README.md).

The directory contexts describe this checkout's definitions. Source declarations
determine exact types and theorem statements; older prose can use earlier names.

## Main relationships

- [Common](Common/CONTEXT.md) defines shared specification-monad machinery;
  [Common.v](Common.v) provides a re-export for its clients.
- [Identity](Identity/CONTEXT.md), [Reader](Reader/CONTEXT.md),
  [ST](ST/CONTEXT.md), and [STEx](STEx/CONTEXT.md) explore individual effects
  and verification judgments through that machinery.
- [Classes](Classes/CONTEXT.md) defines generic arrows and transformer laws.
- [Taxonomy](Taxonomy/CONTEXT.md) separates computation models, specification
  carriers, and observations. Its [README](Taxonomy/README.md) supplies the
  detailed mathematical discussion; local contexts identify the source contracts.

## Shared distinctions

- A computation's outcome type determines which effects are observable.
  Check each option layer before interpreting `None` as exception or divergence.
- A specification carrier, its equality, and its refinement order are separate
  choices. Similarly named judgments can use opposite implication directions.
- Unary specification monads and binary specification arrows have different
  interfaces. Consult the defining module before transferring a law between them.
- Monad laws and observation-preservation lemmas do not by themselves establish
  monotonicity of bind in a chosen order. The Taxonomy contexts identify relevant
  restrictions and counterexamples.

## Build boundaries

The [global map](../CONTEXT-MAP.md) covers every directory containing a
manifest-listed source, together with its parents. Some
[OldSP](Taxonomy/OldSP/CONTEXT.md) sources remain active; `deprecated/`,
`Backup/`, and `ITreeExamples/` are excluded from the manifest.
Use the manifest rather than a directory name to decide which files are active.
