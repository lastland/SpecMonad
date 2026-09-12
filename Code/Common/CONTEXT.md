# Common

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

This directory supplies pre/post orders, predicate specifications, and small
effect models used by the earlier examples. Its `Classes.v` concerns these
specification orders; the generic arrow contracts belong to
[Classes](../Classes/CONTEXT.md).

## Vocabulary and semantic distinctions

- [Classes.v](Classes.v) defines `PreT`, `PostT`, `PrePostT`, their laws,
  `PredMonad`, and `GaloisPrePostPred`. `eqPred` is mutual `ordPred`.
  `PredMonadLaws` supplies preorder/equivalence properties, not monad equations.
- [PureSpecMonads.v](PureSpecMonads.v) defines `PurePre := Prop`,
  `PurePred A := A -> Prop`, and monotone `SPost` transformers whose output
  implies the supplied precondition. `p2pp`, `pp2p`, `p2sp`, and `sp2p`
  connect these presentations.
- In that file, `pp2p (P, Q)` means `fun r => P -> Q r`, and the postcondition
  comparison in `ordPrePost` is conditional on the target precondition.
  [PurePrePostStandard.v](PurePrePostStandard.v) instead compares postconditions
  unconditionally and defines `pp2p (P, Q)` as `Q`.
- [StateSpecMonads.v](StateSpecMonads.v) defines `StatePred S A` as
  `S -> A -> S -> Prop`: initial state, result, final state. Bind existentially
  composes through an intermediate result and state.
- [OptionSpecMonads.v](OptionSpecMonads.v) uses predicates over `option A`.
  Its `bindPred` continues only from `Some a`; it does not add propagation of
  an incoming `None`. This differs from the generic
  [option arrow transformer](../Classes/OptionArrowT/CONTEXT.md).
- [NonDetSpecMonads.v](NonDetSpecMonads.v) uses predicates over predicates,
  `Post A := (A -> Prop) -> Prop`; do not identify it with the unary
  `PurePred` carrier: the local `Pred` has this higher-order shape.
- [PureSpecKleisli.v](PureSpecKleisli.v) explores `Kleisli`, inhabited
  preconditions, and `dualPrePost`. Its monad/comonad laws are marked TODO,
  and attempted inverse/adjunction results include aborted proofs.
- [Guarded.v](Guarded.v) defines `guarded A := { P : Prop & P -> A }` and
  `GuardedMonad`; its `obsPred` universally quantifies over guard proofs.
- [IOStateExc.v](IOStateExc.v) contrasts relational `M` with `W` (weakest
  precondition) and `WP` (weakest possible precondition). `inputW` quantifies
  universally, while `inputWP` quantifies existentially. Exceptions carry
  no final state, and handlers start from the original state.

## Reading and build membership

Start with `Classes.v`, then `PureSpecMonads.v` and the relevant effect file.
[Common.v](../Common.v) re-exports only `Notations`, `Classes`,
`PureSpecMonads`, `StateSpecMonads`, and `OptionSpecMonads`;
[Notations.v](Notations.v) supplies function composition notation.

All source files linked above are listed in [_CoqProject](../_CoqProject).
Consult that manifest before treating additional files as build dependencies.
Build membership is not evidence that exploratory laws have been proved.

Consumers and related examples: [ST](../ST/CONTEXT.md),
[Identity](../Identity/CONTEXT.md), and [STEx](../STEx/CONTEXT.md).
