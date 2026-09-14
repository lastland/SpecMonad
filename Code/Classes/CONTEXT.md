# Classes context

Parent: [Code](../CONTEXT.md). Conventions: [CLAUDE.md](../../CLAUDE.md).

## Contracts

[Arrow.v](Arrow.v) defines pure, sequential composition (first argument runs
first), and `first`; `second`, split, and fanout are derived. `ArrowEq` selects
an equivalence, not necessarily Leibniz equality. `ArrowLaws` includes product
naturality and proper composition/first. Choice has sum laws and proper left.

`ArrowApplyLaws` has static application, `app_unit`, `app_precompose`,
`app_postcompose`, and pair-valued `app_ext`: both the stored arrow's selected
equality and equality of its argument matter. Main compatibility corollaries
`app_pair`, `app_post`, and the curried `app_*_at` forms remain available.
The option and state transformers lift this full contract algebraically.
[ArrowApplyFacts.v](ArrowApplyFacts.v) derives extensional reasoning;
[ArrowMonad.v](ArrowMonad.v) defines operations and laws at every fixed input
`I`, with explicit `Eq1_Arrow HE I`. `bind_arrow_unit` remains a corollary.

[ArrowMorphism.v](ArrowMorphism.v) packages proper operation-preserving maps.
[RelArrowCoherence.v](RelArrowCoherence.v) derives application equations and
bind semantics from faithful relational presentations; it does not add
well-formedness fields to concrete carriers. Loop has its own laws; neither
transformer supplies loop lifting. `ArrowT` alone asserts no preservation laws.

- [RelArrowCoherence.v](RelArrowCoherence.v) separates relational operation
  contracts (`RelArrow`, `RelArrowChoice`, `RelArrowApply`) from `RelArrowEq`,
  which identifies the chosen `arrow_eq` with pointwise relation equivalence.
  The shared `rel_arrow_laws`, `rel_arrow_choice_laws`, and
  `rel_arrow_apply_laws` instances supply complete law packages, including
  `Proper` fields and `app_ext`. Core laws need neither choice nor application;
  choice laws need no application. Concrete SP modules instantiate these
  contracts with recovered or stored relations.
  Relational-only `rel_<equation>_iff` lemmas and state-over-option formulas,
  including `rel_state_option_bind_fields`, do not require faithfulness.
  The exact-equality `rel_<equation>_fields` helpers and `RelArrowPresentation`
  wrappers remain available. `rel_arrow_*_laws_leibniz` transports semantic
  laws when equivalence reflects into ordinary equality; exact morphism
  clients use explicit transported dictionaries rather than changing the
  carrier's selected equality. Transformer laws remain in the generic
  option/state modules.

[Galois.v](Galois.v) relates two ordered binary carriers via alpha/gamma,
preorders, and the adjunction. [OrderedMonad.v](OrderedMonad.v) concerns unary
monads under a specified preorder containing `eq1`, with monotone bind.
Every lawful monad is ordered by its equivalence; stronger orders need proofs.
These differ from [Common/Classes.v](../Common/Classes.v)'s pre/post API.

## Boundaries and tests

Start with `Arrow.v`, then `ArrowApplyFacts.v` and `ArrowMonad.v`, or the
transformer context relevant to the task. The concrete relational carrier is
`Rel A B := A -> B -> Prop` in
[Rel.v](../Taxonomy/Arrows/Rel.v), not a definition in `Arrow.v`.

Read [option](OptionArrowT/CONTEXT.md) or [state](StateArrowT/CONTEXT.md)
contexts after the base contract. Keep explicit dictionaries in recursive
transformer stacks. [Generic tests](Tests/CONTEXT.md) check arrow monads;
[concrete tests](../Taxonomy/Arrows/Tests/CONTEXT.md) check carrier instances.
Classes does not import concrete Taxonomy carriers. The relational carrier
belongs to Taxonomy/Arrows; use its defining module for exact names.
