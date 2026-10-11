# Code context

Parent: [global map](README.md). Conventions: [CLAUDE.md](../../../CLAUDE.md).

[_CoqProject](../../../Code/_CoqProject) maps `Code/` to `Incorrectness` and defines
the normal build boundary. A file's presence does not establish membership.
Dependencies live in [the opam file](../../../Code/coq-spec-monad.opam); follow the current
Makefile for build/audit targets. Source declarations override older prose.

## Ownership

Directories follow the paper ([README](../../../Code/README.md)); each imports only from
the layers listed in [scripts/layers.txt](../../../Code/scripts/layers.txt), checked by
`make layers`.

- [Lib](Lib.md): generic arrow laws, transformers, morphisms,
  fixed-input monads, ordered monads, monadic relations, transformer laws.
  No specification carrier.
- [Relational](Relational.md): relations, their SP readings, `Pred`;
  proof infrastructure below SP.
- [WP](WP.md) and [SP](SP.md): the specification monads
  (paper §2-3).
- [PTMonadTaxonomy](PTMonadTaxonomy.md): the relations of the taxonomy (§4).
- [Verification](Verification.md): everything that involves the computation
  monad, by setting: [Generic](Verification/Generic.md),
  [DivNonDet](Verification/DivNonDet.md), [DivNonDetSt](Verification/DivNonDetSt.md),
  [DivNonDetStExc](Verification/DivNonDetStExc.md) (§1, §5, §6).
- [GaloisConnections](GaloisConnections.md): DM4All monads and
  their adjunctions (§7).
- [Tests](Tests.md): instance and regression checks.
- [Checks](Checks.md) reports selected assumptions and checks the
  paper claims, separately from the build, through `make check` in the
  maintained [Makefile](../../../Code/Makefile). Reporting is not a proof of axiom-freedom;
  context documents are not an assumption ledger.

## Shared distinctions

Check each outcome layer: `None` is not uniformly divergence. Check each
carrier's equality and order: similar names can reverse implication.
Unary monads differ from binary arrows at a fixed input. Well-formedness,
monad laws, monotonicity in a precondition, and ordered bind are separate.
Some exploratory proofs end in `Abort`; build membership does not turn them
into results. `Backup/` (with the former `Taxonomy/deprecated/`) and `ITreeExamples/` are excluded. Follow parent/local contexts and source links.
