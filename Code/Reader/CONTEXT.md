# Reader

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

[Reader.v](Reader.v) observes ExtLib reader computations with forward predicate
transformers. It compares achieved predicates that hide the environment with
ones that retain it; this choice changes what an incorrectness claim requires.

## Established vocabulary and contracts

- ExtLib's `reader S A` is the computation type. The local `Reader S A`
  assigns each environment `s0` and `pre : Prop` a predicate on results,
  together with a proof that the result predicate can hold only if `pre` holds.
- `WFReader S A` additionally requires monotonicity in `pre`;
  `toReader` exposes its underlying `Reader` through a coercion.
- `retReader`, `bindReader`, `askReader`, and `localReader` supply the
  `Monad__Reader` and `MonadReader__Reader` instances for `Reader`.
  Bind uses the same environment throughout; `localReader` changes it for
  its argument.
  The file explicitly leaves monad laws unproved.
- `obsReader m s0 pre r` asserts `runReader m s0 = r /\ pre`.
  `Verify w m obs` means `w s0 pre r -> obs m s0 pre r` at every index:
  the specification implies the observation, opposite to [ST](../ST/CONTEXT.md).
- `Verify_ret`, `Verify_bind`, `Verify_ask`, and `Verify_local` establish
  compositional verification for `obsReader`; the `mst` hint database uses them.

## Achieved predicates and initial environments

`WithStateFreeAchieves.SP presumes w r` existentially hides the environment:
`exists s0, w s0 (presumes s0) r`. Its `Incorrect` requires this witness for
each achieved result. Its `Correct` instead requires every result in `SP`
to satisfy the postcondition.

`WithStateAwareAchieves.SP presumes w s0 r` keeps the environment and applies
`w s0 (presumes s0) r` directly. Its achieved predicates have type
`S -> R -> Prop`, so `Incorrect` checks each asserted environment/result pair.
In both modules, `Incorect_weaken`, `SP_monotone`, and `agreement` require
`WFReader`; do not drop their monotonicity hypothesis.

Keep the older `WithStateFreeAchieves.Incorrect_` separate: for every result,
it chooses `s0` satisfying `presumes`, with `achieves s0 r` inside an implication.
It is not the `achieves r -> exists s0, ...` definition used by `Incorrect`.

## Dependencies and reading

Start with the carrier, operations, and `obsReader`, then choose one of the
two achieved-predicate modules. Their `example_3_1r` / `example_3_1R` names
distinguish computations from specifications; use module qualifiers.
The state-free module's `example_3_1_dijkstra` connects the two via `Verify`.

Reader.v imports ExtLib, Coq arithmetic libraries, and CoqHammer, not Common
or Taxonomy. It is listed in [_CoqProject](../_CoqProject).
