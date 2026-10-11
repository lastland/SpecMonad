# Code context

Parent: [global map](../CONTEXT-MAP.md). Conventions: [CLAUDE.md](../CLAUDE.md).

[_CoqProject](_CoqProject) maps this directory to `Incorrectness` and defines
the normal build boundary. A file's presence does not establish membership.
Dependencies live in [the opam file](coq-spec-monad.opam); follow the current
Makefile for build/audit targets. Source declarations override older prose.

## Ownership

Directories follow the paper ([README](README.md)); each imports only from
the layers listed in [scripts/layers.txt](scripts/layers.txt), checked by
`make layers`.

- [Lib](Lib/CONTEXT.md): generic arrow laws, transformers, morphisms,
  fixed-input monads, ordered monads, monadic relations, transformer laws.
  No specification carrier.
- [Computation](Computation/CONTEXT.md): `divndNE` and its two stacks.
- [Relational](Relational/CONTEXT.md): relations, their SP readings, `Pred`;
  proof infrastructure below SP.
- [WP](WP/CONTEXT.md) and [SP](SP/CONTEXT.md): the specification monads
  (paper §2-3).
- [PTMonadTaxonomy](PTMonadTaxonomy/CONTEXT.md): the relations of the taxonomy (§4).
- [Triples](Triples/CONTEXT.md) and [Dijkstra](Dijkstra/CONTEXT.md):
  monad morphisms, triples, Dijkstra monads (§5-6).
- [GaloisConnections](GaloisConnections/CONTEXT.md): DM4All monads and
  their adjunctions (§7).
- [Tests](Tests/CONTEXT.md): instance and regression checks.
- [Checks](Checks/CONTEXT.md) reports selected assumptions and checks the
  paper claims, separately from the build, through `make check` in the
  maintained [Makefile](Makefile). Reporting is not a proof of axiom-freedom;
  context documents are not an assumption ledger.

## Shared distinctions

Check each outcome layer: `None` is not uniformly divergence. Check each
carrier's equality and order: similar names can reverse implication.
Unary monads differ from binary arrows at a fixed input. Well-formedness,
monad laws, monotonicity in a precondition, and ordered bind are separate.
Some exploratory proofs end in `Abort`; build membership does not turn them
into results. `Backup/` (with the former `Taxonomy/deprecated/`) and `ITreeExamples/` are excluded. Follow parent/local contexts and source links.
