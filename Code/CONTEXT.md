# Coq development context

Start with the [global context map](../CONTEXT-MAP.md). Project goals and status
live in the [root README](../README.md); shared proof conventions live in
[CLAUDE.md](../CLAUDE.md).

## Scope and build membership

[_CoqProject](_CoqProject) maps this directory to the logical namespace
`Incorrectness` and lists the normal build's sources. A `.v` file's presence
alone does not establish that it belongs to that build. Dependency versions
are declared in the [opam manifest](coq-spec-monad.opam).

[Checks](Checks/CONTEXT.md) supplies a separate opt-in assumption audit through
[Makefile.local](Makefile.local). Consult the audit's current output for the
assumptions of selected theorems; context documents are not an assumption ledger.

## Main areas

- [Common](Common/CONTEXT.md) defines shared specification-monad interfaces and
  effect constructions. [Common.v](Common.v) re-exports a selected subset.
- [Classes](Classes/CONTEXT.md) defines generic arrow contracts, algebraic
  transformers, and the arrow-derived monad construction.
- [Taxonomy](Taxonomy/CONTEXT.md) connects concrete effectful computations to
  specification monads and arrows through observations. Its
  [README](Taxonomy/README.md) is the detailed architectural reference.
- [Identity](Identity/CONTEXT.md), [Reader](Reader/CONTEXT.md),
  [ST](ST/CONTEXT.md), and [STEx](STEx/CONTEXT.md) contain built developments
  for particular effects and specification styles. Their local interfaces
  and verification directions should be read in their own contexts.

## Domain distinctions

A computation describes possible behavior; a specification constrains it.
An observation connects the two. Generic laws describe the required algebraic
contract independently of a concrete computation. In the Taxonomy development,
specifications depend on outcome types, and observations introduce dependencies
on concrete computation monads. The generic transformer laws happen to live
under `Taxonomy/ComputationMonads/` without naming a concrete computation.

Use **well-formedness** for constraints on SP transformers. Do not transfer
the meaning of `None`, a refinement order, or a `Verify` judgment between
developments without checking its definition.

## Where to start

For SP/WP semantics, start with [Taxonomy](Taxonomy/CONTEXT.md). For generic
arrow laws or transformer resolution, start with [Classes](Classes/CONTEXT.md).
For shared specification-monad APIs, start with [Common](Common/CONTEXT.md).
Use the [global map](../CONTEXT-MAP.md) to locate leaf contexts and historical
areas. In particular, `Taxonomy/OldSP/` is partly built, while
`Taxonomy/deprecated/`, `Backup/`, and the copied `ITreeExamples/` are outside
the normal build.
