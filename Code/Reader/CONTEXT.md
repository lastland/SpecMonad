# Reader

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and definitions

[Reader.v](Reader.v) studies forward specifications for ExtLib's reader
computation, including whether an achieved predicate can mention its input
environment. Lowercase `reader S A` is the computation type; uppercase
`Reader S A` is the local specification type.

- `Reader` takes an environment `s0` and propositional precondition, then
  returns a result predicate whose truth implies that precondition.
- `WFReader` additionally bundles monotonicity in the precondition.
  `toReader` is the coercion to the underlying specification.
- `retReader`, `bindReader`, `askReader`, and `localReader` supply `Monad`
  and `MonadReader` operations. Bind shares the environment; `localReader`
  changes it for the nested specification. Monad laws are explicitly unproved.
- `obsReader` observes `runReader m s0 = r` together with the precondition.
  `Verify w m obs` requires `w` to imply the observation, an underapproximation
  direction. `Verify_ret`, `Verify_bind`, `Verify_ask`, and `Verify_local`
  support compositional proofs.

## Two achieved-predicate interfaces

`WithStateFreeAchieves.SP` existentially hides the initial environment and
has result type `R -> Prop`. Its `Incorrect` includes `achieves` in `SP`.
`WithStateAwareAchieves.SP` retains the environment and has result type
`S -> R -> Prop`; the achieved predicate must account for the presumption
at that same environment.

Both modules define the dual `Correct` direction and prove weakening,
disjunction, and agreement results. Monotonicity-dependent results require
`WFReader`. The separate `Incorrect_` definition is an explored alternative
with a different quantifier shape, not an alias for `Incorrect`.

## Reading and dependencies

Read `Types`, the operations, and `obsReader`/`Verify` first; then compare
the two modules and their `example_3_1` proofs. The file depends on ExtLib,
CoqHammer, and Coq arithmetic and is listed in [_CoqProject](../_CoqProject).

Related contexts: [Identity](../Identity/CONTEXT.md) for the pure input-context
comparison, [ST](../ST/CONTEXT.md) for mutable-state observations, and
[STEx](../STEx/CONTEXT.md) for a similar `Verify` direction with exceptions.
