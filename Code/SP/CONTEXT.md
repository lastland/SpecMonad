# Base specification monads context

Parent: [Taxonomy](../CONTEXT.md). Related: [arrows](../Arrows/CONTEXT.md).
Source declarations determine exact types, selected dictionaries, and orders.

## Shared unary specifications

Every monad file owns its refinement order and the proof that the monad is a
specification monad under it (`OrderedMonad_*`); there is no separate summary
file. The table under "Orders and comparisons" lists the verdicts.

- PredMonad: unary PredM.Pred and state/option predicate stacks, with
  `Pred_le` / `ordPredStExc` and `OrderedMonad_Pred` / `OrderedMonad_PredStExc`.
- PrePostMonad: PPM.PrePost pairs propositional pre with a result predicate;
  bind checks continuations universally and collects results existentially.
  `PP_le` and `OrderedMonad_PrePost` are at the end of the file.
- SPostMonad: SPM.SPost bundles monotone transformers into Over pre,
  propositions implying that precondition. It is not a binary SP arrow.
  `SP_le` and `OrderedMonad_SPost` follow the monad laws.
- WPureMonad: monotone weakest-precondition transformers, exposed by getWPure,
  with state/option stacks. WP_le and its generic lifts are reverse
  implication. `OrderedMonad_WPure`, `OrderedMonad_WSt` and
  `OrderedMonad_WStExc` are here, and the four flavours AWP, DWLP,
  DWP, AWLP are ordered as its submonads: `OrderedMonad_WPSub` is
  `OrderedMonad_pullback` along `toWPure`. Keep the corresponding WP triple argument/direction changes.
  The file also carves AWP, DWLP, DWP, and AWLP out of WPure as submonads by
  healthiness (`WPHealth`, `WPSub`), with state stacks and both orders.
- RelPrePostMonad: validators into Assuming pre, whose propositions satisfy
  `q <-> (pre -> q)`, with Hoare-order monotonicity. `MR_le` and
  `OrderedMonad_RelPrePost` are at the end of the file.

## Raw SP carriers

SPPredicateTransformers defines raw SPPure, shared-precondition SPSt, and
option-indexed SPStExc, their healthiness predicates, and the skew-monadic
structures on monotone stateful transformers. They are not the carriers of
the four SP monads below, which come from the arrows.

- [`WPureT` / `WPure`](WPureMonad.v) distinguish the raw WP transformer
  from its monotone subset. `WSt` and `WStExc` stack state and optional
  exceptions over `WPure`; `getWPure` exposes application.

## Four-flavour public API

The four public monads consume [Arrows/SPostArr.v](../Arrows/SPostArr.v), which
implements `ASPArr`, `DSLPArr`, `DSPArr`, and `ASLPArr`, their operations,
recovered relations, laws, binary stacks, and conversions. `SPostArr.v` does
not depend on this directory, including `SPure.v`. Its ASP/DSLP normal forms
and semantic law packages are constructive; DSP/ASLP recovery is classical.
The selected equalities are transformer iff, not Leibniz bundle equality.
The `PureASPostArr` / `PureDSLPostArr` compatibility aliases and their plain
dictionary definitions add neither a second carrier nor instance registrations.

## Arrow-derived monad consumers

`ASPMonad.v`, `DSLPMonad.v`, `DSPMonad.v`, and `ASLPMonad.v` fix input `unit`
and use generic `Classes/ArrowMonad.v` operations and laws. Each exposes
pure/state/state-option monads, runners, refinement orders, ordered-bind proofs,
and monad-specific results. Qualify unary accessors such as `ASPMonad.getASP`
against the binary `SPostArr.getASP` (and likewise for DSLP).

`DSPMonad.v` and `ASLPMonad.v` close with the pure collapse. At input `unit`
the DSP and ASP healthiness conditions coincide, and so do the ASLP and DSLP
ones; `dsp_to_asp` / `asp_to_dsp` and `aslp_to_dslp` / `dslp_to_aslp` are the
identity on transformers, mutually inverse, and preserve `ret`, `bind`, and the
pointwise orders. Only ASP-to-DSP is constructive. `OrderedMonad_DSP` and
`OrderedMonad_ASLP` pull the orders of ASP and DSLP back along these maps, so
without state DSP and ASLP are specification monads.

Each of the four files ends with the stateless monad defined directly on
`SPPure A = Prop -> A -> Prop`: `ASPSP` (`Singleton`), `DSLPSP`
(`MSingleton`), and `DSPSP` / `ASLPSP`, which are those two under the
strict-conjunctive / terminating-disjunctive presentation with the monad
structure transported. Their operations carry the suffix `SP`
(`retASPSP`, `bindASPSP`, `getASPSP`), because `retASP`, `bindASP`, `getASP`
belong to the arrow-derived monad. `aspsp_to_asp` / `asp_to_aspsp` and the
three analogous pairs show that each direct monad is the arrow-derived one:
mutually inverse monad morphisms that preserve and reflect the order. There
is no direct definition with state or with exceptions.

[MonadTaxonomy.v](MonadTaxonomy.v) places the SP and WP carriers inside
`MonoPT` and states implication, contrapositive, and Galois connection as
monadic relations ([Classes/MonadRelation.v](../../Classes/MonadRelation.v)):
on WPure and its transformer stacks, on SPStMon with its angelic and demonic
structures, and between the flavour monads at the pure, state, and state-option
stacks. DSP and ASLP enter SP implications through one part, because bind does
not preserve their pointwise orders. `GaloisSPWP` / `GaloisWPSP` are `Ladj` /
`Radj` of SPPredicateTransformers; use the bridge lemmas, never the admitted
`Radj_bind`. Name the angelic or demonic SPStMon structure explicitly.
Every flavour instance that involves an SP monad goes through the relation the
SP element denotes: implication is inclusion and contrapositive is equality of
the denoted relations, each one index-generic lemma. A Galois instance is the
base relation between `PredM.Pred` and `WPure` (`GaloisPredWP`,
`GaloisWPPred`), lifted by the monad transformers on the WP side and read at
the denoted results on the SP side (`MonadRelation_rel_pred` and its two stack
versions). The Galois instances use no axiom.

The canonical `ASPStExc` / `DSLPStExc` monads are definitionally the
compatibility `ASPostArr` / `DSLPostArr` stacks of `SPostArr.v`, which also
has the binary `asp_to_dslp` conversion and its relation-reading facts. That
an ASP element and the DSLP element denoting the same relation correspond
under `ret` and `bind` is `MonadRelation_contra_asp_dslp_exc_one` / `_two` in
`MonadTaxonomy.v` (and its state and stateless versions); there is no
separate bridge file.

[SPure.v](SPure.v) owns only unary relational monads, return/bind facts, and
orders. [Rel.v](../Arrows/Rel.v) owns the binary relation carrier, stacks, and
congruence; [RelSPostArr.v](../Arrows/RelSPostArr.v) owns the four SP readings.
Generic normalization (`rel_bind`, `relS_bind`, `relO_*`, `relE_*`) lives in
[RelArrowCoherence.v](../../Classes/RelArrowCoherence.v) and uses the existing
`RelArrow` / `RelArrowChoice` / `RelArrowApply` contracts. `SPostArr.v` specializes
these facts for its canonical relation-reading wrappers.

- [DSPMonad.v](DSPMonad.v) and [ASLPMonad.v](ASLPMonad.v) refute the ordered
  monad laws for `DSPSt` / `ASLPSt` and `DSPStExc` / `ASLPStExc` under their
  pointwise orders (`not_OrderedMonad_*`). Monad laws still hold.
  `dsp_arbitrary_bind_impossible` and `aslp_arbitrary_bind_impossible`
  strengthen this for Boolean state: no candidate Boolean-to-unit bind
  satisfies both left identity for the monad's return and first-argument
  monotonicity. The contradiction uses only that the candidate's output is in
  the carrier, independently of the existing bind.

## Orders and comparisons

ASP's transformer order follows relation inclusion; DSLP reverses it. Their
pointwise orders carry OrderedMonad. DSP and ASLP carry no OrderedMonad with
state: their pointwise orders fail it (`not_OrderedMonad_DSPSt`,
`not_OrderedMonad_ASLPSt`, and the `StExc` pair), and a predicate-transformer
monad is ordered by its own order or not at all. Without state they are
ordered, as ASP and DSLP.

| monad | order | ordered? | proved in |
|---|---|---|---|
| `PredM.Pred`, `PredStExc S` | `Pred_le`, `ordPredStExc` | yes | `PredMonad.v` |
| `PPM.PrePost` | `PP_le` | yes | `PrePostMonad.v` |
| `SPM.SPost` | `SP_le` | yes | `SPostMonad.v` |
| `RPPM.RelPrePost` | `MR_le` | yes | `RelPrePostMonad.v` |
| `WPure`, `WSt S`, `WStExc S` | `WP_le`, `ordWSt`, `ordWStExc` | yes | `WPureMonad.v` |
| `ASP`, `ASPSt S`, `ASPStExc S`, `ASPSP` | pointwise | yes | `ASPMonad.v` |
| `DSLP`, `DSLPSt S`, `DSLPStExc S`, `DSLPSP` | pointwise | yes | `DSLPMonad.v` |
| `DSP`, `DSPSP` / `ASLP`, `ASLPSP` | pointwise | yes | `DSPMonad.v` / `ASLPMonad.v` |
| `DSPSt S`, `DSPStExc S` / `ASLPSt S`, `ASLPStExc S` | pointwise | no | `DSPMonad.v` / `ASLPMonad.v` |

BaseGaloisConnections relates the unary DM4All presentations through their
orders, including both adjunctions between `PrePost` and `WPure`.
SPStBindComparisons studies skew-monadic/functor structure and bind comparisons.
Read the chosen carrier, operations, equality, and order before observations.
