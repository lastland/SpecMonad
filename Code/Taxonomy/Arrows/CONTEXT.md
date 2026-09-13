# Specification arrows context

Parent: [Taxonomy](../CONTEXT.md). Related: [Classes](../../Classes/CONTEXT.md),
[base specifications](../BaseSpecMonads/CONTEXT.md), and [README](../README.md).

## Carriers

- The relational carrier in Rel.v is `A -> B -> Prop`, with existential
  composition and pointwise iff equality. Its fixed-input bind shares the
  input: `exists b, m i b /\ k b i c`. Option/state stacks are separate
  from unary PredM.Pred. Read its module for exact names during renames.
- PrePostArr pairs a precondition and an input-indexed post-relation;
  equality compares both by iff, while order reverses pre implication.
- SPArrT is the raw `(A -> Prop) -> B -> Prop`. Its monotone/strict/terminating/
  conjunctive/disjunctive properties do not supply a generic arrow instance.
  Conjunctive/disjunctive families are nonempty; strict/top preservation cover
  the empty cases where required.
- WPArr is a reader-WP Kleisli arrow over the raw WPureT, with Leibniz equality
  and reverse pointwise order. RelPrePostArr validates Hoare specs;
  project_wp compares operations/laws but not every raw validator verdict.

## SP presentations and monads

SPostArr contains only transformers and well-formedness proofs: PureASPostArr
is strict/disjunctive; PureDSLPostArr is terminating/conjunctive. Their direct
operations have constructive existential/universal normal forms. Unreachable
outputs make ASP false and DSLP true. Equality is Leibniz on bundles.

RelSPPairArr couples spost and rel in RelSPPair. PureRelASPPairArr /
PureRelDSLPPairArr require agreement with the ASP/DSLP reading. Constructors
mkASP/mkDSLP package relations; bundled equality recovers both components.
SPostArrEquiv proves operation-preserving equivalence with the property-only
presentation. Qualify shared stack names when importing both.

SPostArrMonad supplies selected generic dictionaries, recovered relations,
observation runners, and the ASP-to-DSLP monad map. Classes/ArrowMonad owns
generic return/bind and laws at arbitrary fixed input; unit-input clients
instantiate these rather than maintaining a duplicate generic implementation.
OptionLoop studies loop transport and obstructions separately from monad laws.
RelArrowCoherence derives application coherence from relational operation
semantics. Transformer law proofs are generic, not concrete carrier inspections.

Main's ASPArr/DSLPArr/DSPArr/ASLPArr in BaseSpecMonads are retained distinct
public bundles; their equality is transformer iff, not the property-only
bundle's Leibniz equality. Canonical-carrier consolidation is not yet done.
[OptionLoop.v](OptionLoop.v), `optionRel_no_left_tightening`, rules out lawful
`ArrowLoop` for the existing `optionRel` operations and pointwise equivalence
when feedback ranges over all types, including `Empty_set`. Empty feedback hides
the difference between an empty prefix and one returning `None`, while option
composition outside the loop distinguishes them. `SPostArrEquiv.v` transports
this obstruction to property-only option ASP and DSLP arrows. Its scope is this
unrestricted law and these operations, rather than every possible feedback design.

## Orders, boundaries, and clients

GaloisArr refines raw carriers as MonotoneWP, WFRelPrePost, and MonotoneSPost.
Preserve subtype hypotheses; a relation/SP adjunction does not identify every
monotone transformer with relational ASP. gamma_uni_not_monotone is an
obstruction; subsequent experimental commentary is not another theorem.

Relational modules can import computation semantics, and WPArr imports a base
specification module: distinguish ownership from the current import graph.
Read constructors → equality/laws → chosen monad dictionaries/orders →
[examples](Examples/CONTEXT.md) and [tests](Tests/CONTEXT.md).
Start with the properties, then `SPostArr.v`, then the
[checked clients](Examples/CONTEXT.md); read `SPostArrEquiv.v` for representation
changes and `SPostArrMonad.v` for observation-facing use.
For other carriers, [Rel.v](Rel.v) defines relations,
[PrePostArr.v](PrePostArr.v) pairs a precondition with an input-indexed
post-relation, and [RelPrePostArr.v](RelPrePostArr.v) defines validators whose
arrow equality compares `project_wp` behavior.
[WPArr.v](WPArr.v) uses raw `WPureT`, not the monotone `WPure` subset.
[GaloisArr.v](GaloisArr.v) is the entrypoint for their refinement orders,
restricted adjunctions, and binary-arrow counterexamples.
