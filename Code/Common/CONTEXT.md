# Common context

Parent: [Code](../CONTEXT.md). This earlier specification-order API differs
from [generic arrow Classes](../Classes/CONTEXT.md) and Taxonomy carriers.

- [Classes.v](Classes.v) defines PreT/PostT/PrePostT, PredMonad, and
  GaloisPrePostPred. `eqPred` is mutual order; PredMonadLaws supplies
  preorder/equivalence, not monad equations.
- [PureSpecMonads.v](PureSpecMonads.v) has `PurePre := Prop`, unary PurePred,
  and monotone SPost whose output implies the precondition. Its
  `pp2p (P,Q)` is `fun r => P -> Q r`, with post-order conditional on the
  target precondition. [PurePrePostStandard.v](PurePrePostStandard.v)
  instead compares posts unconditionally and uses Q alone.
- [StateSpecMonads.v](StateSpecMonads.v)'s relation indices are initial
  state/result/final state; bind composes existentially. `pp2p` guards
  the post-relation with the initial precondition.
- [OptionSpecMonads.v](OptionSpecMonads.v) continues only from Some and
  does not propagate an incoming None, unlike OptionArrowT.
- [NonDetSpecMonads.v](NonDetSpecMonads.v) uses predicates on predicates,
  `(A -> Prop) -> Prop`, not unary PurePred.
- [PureSpecKleisli.v](PureSpecKleisli.v) explores Kleisli, inhabited
  preconditions, and dualPrePost; TODOs/aborted proofs are not results.
- [Guarded.v](Guarded.v) stores `{ P : Prop & P -> A }`; obsPred is universal
  over guard proofs.
- [IOStateExc.v](IOStateExc.v) contrasts relational M with universal W and
  existential WP. Outcomes are `A * S + E`; exceptions have no final state,
  and handlers use the initial state.

[Common.v](../Common.v) re-exports Notations, Classes, PureSpecMonads,
StateSpecMonads, and OptionSpecMonads only. Other modules need imports.
Read the chosen carrier and order before [ST](../ST/CONTEXT.md),
[Identity](../Identity/CONTEXT.md), or [STEx](../STEx/CONTEXT.md) clients.
Consult [_CoqProject](../_CoqProject) rather than counting local files.
