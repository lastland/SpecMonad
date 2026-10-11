# Code context

Parent: [global map](../CONTEXT-MAP.md). Conventions: [CLAUDE.md](../CLAUDE.md).

[_CoqProject](_CoqProject) maps this directory to `Incorrectness` and defines
the normal build boundary. A file's presence does not establish membership.
Dependencies live in [the opam file](coq-spec-monad.opam); follow the current
Makefile for build/audit targets. Source declarations override older prose.

## Ownership

- [Classes](Classes/CONTEXT.md) supplies generic arrow laws, transformers,
  morphisms, and fixed-input monads without concrete Taxonomy carriers.
- [Taxonomy](Taxonomy/CONTEXT.md) separates computation outcomes, base
  specifications, concrete binary arrows, monad morphisms with their triples,
  and Dijkstra monads.
- [Checks](Checks/CONTEXT.md) reports selected assumptions separately from
  normal tests/examples through `make check` in the maintained [Makefile](Makefile).
  Reporting is not a proof of axiom-freedom; context documents are not an
  assumption ledger.

## Shared distinctions

Check each outcome layer: `None` is not uniformly divergence. Check each
carrier's equality and order: similar names can reverse implication.
Unary monads differ from binary arrows at a fixed input. Well-formedness,
monad laws, monotonicity in a precondition, and ordered bind are separate.
Some exploratory proofs end in `Abort`; build membership does not turn them
into results. `Backup/` (with the former `Taxonomy/deprecated/`) and `ITreeExamples/` are excluded. Follow parent/local contexts and source links.
