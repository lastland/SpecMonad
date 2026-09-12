# Code context

Parent: [global map](../CONTEXT-MAP.md). Conventions: [CLAUDE.md](../CLAUDE.md).

[_CoqProject](_CoqProject) maps this directory to `Incorrectness` and defines
the normal build boundary. A file's presence does not establish membership.
Dependencies live in [the opam file](coq-spec-monad.opam); follow the current
Makefile for build/audit targets. Source declarations override older prose.

## Ownership

- [Common](Common/CONTEXT.md) supplies earlier specification interfaces.
- [Classes](Classes/CONTEXT.md) supplies generic arrow laws, transformers,
  morphisms, and fixed-input monads without concrete Taxonomy carriers.
- [Identity](Identity/CONTEXT.md), [Reader](Reader/CONTEXT.md),
  [ST](ST/CONTEXT.md), and [STEx](STEx/CONTEXT.md) study individual effects.
- [Taxonomy](Taxonomy/CONTEXT.md) separates computation outcomes, base
  specifications, concrete binary arrows, observations, and comparisons.
- [Checks](Checks/CONTEXT.md) reports selected assumptions separately from
  normal tests/examples. Reporting is not a proof of axiom-freedom.

## Shared distinctions

Check each outcome layer: `None` is not uniformly divergence. Check each
carrier's equality and order: similar names can reverse implication.
Unary monads differ from binary arrows at a fixed input. Well-formedness,
monad laws, monotonicity in a precondition, and ordered bind are separate.
Some exploratory proofs end in `Abort`; build membership does not turn them
into results. `OldSP` is partly built; `deprecated/`, `Backup/`, and
`ITreeExamples/` are excluded. Follow parent/local contexts and source links.
