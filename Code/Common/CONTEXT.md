# Common

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

Common supplies predicate specifications, pre/post orders, and small effect
models. Its order classes are distinct from the generic arrow contracts in
[Classes](../Classes/CONTEXT.md); similarly named Taxonomy carriers are
separate definitions.

## Established vocabulary and contracts

- [Classes.v](Classes.v) defines `PreT`, `PostT`, `PrePostT`, and their
  reasoning laws. `PredMonad` bundles monad operations with `ordPred`;
  `eqPred` means mutual `ordPred`. `PredMonadLaws` supplies preorder and
  equivalence properties, not the return/bind equations.
- `GaloisPrePostPred` supplies `p2pp` and `pp2p`;
  `GaloisPrePostPredLaws` relates predicate inclusion to the pre/post order.
- [PureSpecMonads.v](PureSpecMonads.v) defines `PurePre := Prop` and
  `PurePred A := A -> Prop`. Its `SPost` packages monotone forward
  transformers whose output implies the supplied precondition;
  `p2sp` and `sp2p` connect these transformers to predicates.
- The pure `pp2p (P, Q)` means `fun r => P -> Q r`. Its `ordPrePost`
  compares postconditions only under the target precondition. In contrast,
  [PurePrePostStandard.v](PurePrePostStandard.v) compares postconditions
  unconditionally and maps `pp2p (P, Q)` to `Q` alone.
- [StateSpecMonads.v](StateSpecMonads.v) defines
  `StatePred S A := S -> A -> S -> Prop`: initial state, result, final state.
  `bindPred` composes through an existential intermediate result and state;
  `pp2p` guards the post-relation with the initial-state precondition.
- [OptionSpecMonads.v](OptionSpecMonads.v) uses `OptionPred A := option A -> Prop`.
  Its `bindPred m k r` requires `exists a, m (Some a) /\ k a r`.
  It does not propagate an incoming `None`, unlike
  [OptionArrowT](../Classes/OptionArrowT/CONTEXT.md).
- [NonDetSpecMonads.v](NonDetSpecMonads.v) uses
  `Post A := (A -> Prop) -> Prop`, also the local `Pred` carrier.
  This is a predicate on predicates, not the unary `PurePred` carrier.
- [PureSpecKleisli.v](PureSpecKleisli.v) explores `Kleisli`, preconditions
  with witnesses, and `dualPrePost`. Monad/comonad laws remain TODOs;
  the attempted inverse and adjunction proofs ending in `Abort` are not results.
- [Guarded.v](Guarded.v) defines `guarded A := { P : Prop & P -> A }`
  and `GuardedMonad`. Its `obsPred` quantifies universally over guard proofs.
- [IOStateExc.v](IOStateExc.v) defines relational computations `M`, weakest
  preconditions `W`, and weakest possible preconditions `WP`.
  `inputW` quantifies universally; `inputWP` existentially. Outcomes use
  `A * S + E`: exceptions carry no final state, and handlers use the initial state.

## Dependencies and boundaries

[Common.v](../Common.v) re-exports only `Notations`, `Classes`,
`PureSpecMonads`, `StateSpecMonads`, and `OptionSpecMonads`.
[Notations.v](Notations.v) defines function composition notation.
Other Common modules require separate imports; repeated short names such as
`SPost` and `bindPred` must be read in their defining module.

Start with `Classes.v`, then the relevant carrier and its order. ExtLib supplies
monad interfaces; CoqHammer supports proofs. [ST](../ST/CONTEXT.md) imports
Common.v. All ten local `.v` files appear in [_CoqProject](../_CoqProject).
