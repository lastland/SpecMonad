# Classes context

Parent: [Code](../CONTEXT.md). Conventions: [CLAUDE.md](../../CLAUDE.md).

## Contracts

[Arrow.v](Arrow/Arrow.v) defines pure, sequential composition (first argument runs
first), and `first`; `second`, split, and fanout are derived. `ArrowEq` selects
an equivalence, not necessarily Leibniz equality. `ArrowLaws` includes product
naturality and proper composition/first. Choice has sum laws and proper left.
The core helpers `first_constant` and `pure_comp_ext` take ordinary pure-function
congruence explicitly, so callers can supply congruence independently of
application laws. `arr_pure_ext` supplies the functional-extensionality-based
form; `ArrowApplyFacts.pure_ext` derives the same congruence constructively
from application coherence.

`ArrowApplyLaws` has static application, `app_unit`, `app_precompose`,
`app_postcompose`, and pair-valued `app_ext`: both the stored arrow's selected
equality and equality of its argument matter. Main compatibility corollaries
`app_pair`, `app_post`, and the curried `app_*_at` forms remain available.
The option and state transformers lift this full contract algebraically.
[ArrowApplyFacts.v](Arrow/ArrowApplyFacts.v) derives extensional reasoning;
its `app_constant` needs only the fixed-arrow application equation alongside
core laws. The dynamic-pure fact `app_constant_unit` uses application coherence.
[ArrowMonad.v](Arrow/ArrowMonad.v) defines operations and laws at every fixed input
`I`, with explicit `Eq1_Arrow HE I`. `bind_arrow_unit` remains a corollary.

[ArrowMorphism.v](Arrow/ArrowMorphism.v) packages proper operation-preserving maps;
`arrow_morphism_monad` turns one into a monad morphism between the
arrow-derived monads at any fixed input.
[RelArrowCoherence.v](Arrow/RelArrowCoherence.v) derives application equations and
bind semantics from faithful relational presentations; it does not add
well-formedness fields to concrete carriers. Loop has its own laws; neither
transformer supplies loop lifting. `ArrowT` alone asserts no preservation laws.

- [ArrowMorphism.v](Arrow/ArrowMorphism.v) uses an ordinary `ArrowMorphism` record
  with explicit operation and equality dictionaries:
  `ArrowMorphism SA SC SX SE DA DC DX DE map`. `SE` and `DE` select the source
  and destination `ArrowEq`. `morphism_proper` maps source-equivalent arrows
  to destination-equivalent arrows. The five preservation fields,
  `morphism_pure`, `morphism_comp`, `morphism_first`, `morphism_left`, and
  `morphism_app`, use the destination `arrow_eq`. Application preservation
  also maps the embedded arrow in the input.
  Inverse morphisms and option/state lifts reuse this record and the selected
  law dictionaries, not a separate exact-equality contract:
  - `inverse_morphism` requires semantic round trips, properness of the back
    map, and destination core/choice/application laws. Inverse application
    uses `app_ext` to replace equivalent embedded arrows.
  - `option_arrow_morphism` requires destination core/choice laws.
  - `state_arrow_morphism` requires destination core/application laws,
    including the law-derived `pure_ext`.
  - `state_option_arrow_morphism` requires all three destination law packages.

  `ArrowEq_leibniz` remains an ordinary definition for independent consumers;
  direct-Rel equivalences do not use it.
- [RelArrowCoherence.v](Arrow/RelArrowCoherence.v) separates relational operation
  contracts (`RelArrow`, `RelArrowChoice`, `RelArrowApply`) from `RelArrowEq`,
  which identifies the chosen `arrow_eq` with pointwise relation equivalence.
  The shared `rel_arrow_laws`, `rel_arrow_choice_laws`, and
  `rel_arrow_apply_laws` instances supply complete law packages, including
  `Proper` fields and `app_ext`. Core laws need neither choice nor application;
  choice laws need no application. Property-only SP arrows instantiate these
  contracts with recovered relations. The relational carrier reuses its
  existing laws in [Rel.v](../Relational/Rel.v).
  Relational-only `rel_<equation>_iff` lemmas and state-over-option formulas,
  including `rel_state_option_bind_fields`, do not require faithfulness.
  The exact-equality `rel_<equation>_fields` helpers and `RelArrowPresentation`
  wrappers remain independent APIs. `rel_arrow_laws_leibniz` and
  `rel_arrow_choice_laws_leibniz` transport semantic laws when equivalence
  reflects into ordinary equality. These
  helpers do not change the carrier's selected equality, and the direct-Rel
  morphisms do not use them. Transformer laws remain in the generic
  option/state modules.

[Galois.v](Galois.v) relates two ordered binary carriers via alpha/gamma,
preorders, and the adjunction. [OrderedMonad.v](Monad/OrderedMonad.v) concerns unary
monads under a specified preorder containing `eq1`, with monotone bind.
Every lawful monad is ordered by its equivalence; stronger orders need proofs.
An ordered monad stays one with its order flipped (`OrderedMonad_flip`). Its
order pulled back along a monad morphism orders the source
(`OrderedMonad_pullback`); a submonad, the elements satisfying a predicate
closed under `ret` and `bind`, is the case of the inclusion
(`SubMonad`, `OrderedMonad_SubMonad`).

The same file defines monad morphisms. `MonadMorphism` is a record of
properness and `ret` / `bind` preservation over explicit dictionaries;
`MonadMorphism_of_laws` builds one for the finest source equality.
`IsMonadMorphism θ` bundles a map with the structures it is a morphism for,
so that the morphism is found from the map alone. The general triple over
such a map is not here: it is in
[Triples/Triple.v](../Triples/Triple.v).

[MonadRelation.v](Monad/MonadRelation.v) states DM4All's monadic relation for any two
monads: a family of relations that holds at `ret` and is preserved by `bind`.
The order of an ordered monad is one. A monadic relation lifts pointwise
through `stateT` and `optionT`. For two arrows with relational
semantics, inclusion or equality of the denoted relations is one between the
arrow-derived monads at the base, `stateArrT`, and `stateArrT`-over-`optionArrT`
stacks. The reading is always the base arrow's: no transformed arrow gets a
`RelArrow` instance. Pass every dictionary explicitly in this file.

## Boundaries and tests

Start with `Arrow.v`, then `ArrowApplyFacts.v` and `ArrowMonad.v`, or the
transformer context relevant to the task. The concrete relational carrier is
`Rel A B := A -> B -> Prop` in
[Rel.v](../Relational/Rel.v), not a definition in `Arrow.v`.

Read [option](Arrow/OptionArrowT/CONTEXT.md) or [state](Arrow/StateArrowT/CONTEXT.md)
contexts after the base contract. Keep explicit dictionaries in recursive
transformer stacks. [Generic tests](../Tests/CONTEXT.md) check arrow monads;
[concrete tests](../Tests/CONTEXT-arrows.md) check carrier instances.
Classes does not import concrete Taxonomy carriers. The relational carrier
belongs to Taxonomy/Arrows; use its defining module for exact names.
