# Base specification monads context

Parent: [Taxonomy](../CONTEXT.md). Related: [arrows](../Arrows/CONTEXT.md).
Source declarations determine exact types, selected dictionaries, and orders.

## Shared unary specifications

- PredMonad: unary PredM.Pred and state/option predicate stacks.
- PrePostMonad: PPM.PrePost pairs propositional pre with a result predicate;
  bind checks continuations universally and collects results existentially.
- SPostMonad: SPM.SPost bundles monotone transformers into Over pre,
  propositions implying that precondition. It is not a binary SP arrow.
- WPureMonad: monotone weakest-precondition transformers, exposed by getWPure,
  with reader/state/option stacks. WP_le and its generic lifts are reverse
  implication. Keep the corresponding WP triple argument/direction changes.
- RelPrePostMonad: validators into Assuming pre, whose propositions satisfy
  `q <-> (pre -> q)`, with Hoare-order monotonicity.

## Earlier SP monads

SPPredicateTransformers defines raw SPPure, shared-precondition SPSt, and
option-indexed SPStExc. Their earlier well-formed monads live in OldMonads,
not the new top-level modules with the same names. Import/qualify deliberately.

- [`DSPDivExc` / `ASLPDivExc`](DivExcSP.v) stack two `optionT` layers over
  pure `DSPSP` / `ASLPSP`. Their runners take `Prop` preconditions and
  `option (option A)` outcomes; the full-outcome observation assigns separate
  indices to successful return, exception, and divergence. `bindDSP_mono` /
  `bindASLP_mono` prove pure bind monotonicity in both arguments;
  `bindDSPDivExc_mono` / `bindASLPDivExc_mono` lift it through both layers.
- [`WPureT` / `WPure`](WPureMonad.v) distinguish the raw WP transformer
  from its monotone subset. `WSt` and `WStExc` stack state and optional
  exceptions over `WPure`; `getWPure` exposes application.
- [`NewGaloisConnections.v`](NewGaloisConnections.v) supplies `Over`/`Under`
  targets and generic triple characterizations. Its `StSP` and `PureSP`
  modules adapt these to state-only and pure outcomes.

Old ASP uses SingletonProg (strict/disjunctive); DSLP uses MSingletonProg
(top-preserving/conjunctive). Old DSP is strict/conjunctive; ASLP is
top-preserving/disjunctive. Nonempty indexed families are intentional.
DSP/ASLP state binds recover relations before composing; do not replace them
with ordinary forward transformer composition. Pure DSPSP/ASLPSP collapse to
ASP/DSLP via property equivalences; reader lifts preserve this per environment.
StASP/StDSLP/StDSP/StASLP supply state-only variants.

## Earlier-carrier recovery proof ownership

[OldMonads/DSPMonad.v](OldMonads/DSPMonad.v) and [OldMonads/ASLPMonad.v](OldMonads/ASLPMonad.v) each share local,
outcome-generic recovery and congruence proofs between their option-outcome and
`StDSP` / `StASLP` presentations. Callers use the specialized `dsp_recov` /
`aslp_recov` and `dsp_cong` / `aslp_cong` lemmas; the generic helpers are
implementation details.

`dsp_comp_recov_option` and `aslp_comp_recov_option` eliminate recovery from
option-outcome relational composition. They reuse `comp_cong` and recovery;
observation proofs lift the resulting equivalence with specialized congruence
and combine it with `bindDSPProg_dsp` / `bindASLPProg_aslp`. Pair-outcome clients
use `StDSP.comp_cong` and their specialized recovery lemmas directly.

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

[SPostArrMonad.v](SPostArrMonad.v) is the unary observation bridge: named
`Monad_ASPostArr` / `Monad_DSLPostArr` dictionaries, `runASP` / `runDSLP`, and
unit-input return/bind conversion results. Its binary `asp_to_dslp` conversion
and relation-reading facts live in `SPostArr.v`. The canonical `ASPStExc` /
`DSLPStExc` monads are definitionally the compatibility `ASPostArr` /
`DSLPostArr` stacks, including their named monad dictionaries and runners.

[SPure.v](SPure.v) owns only unary relational monads, return/bind facts, and
orders. [Rel.v](../Arrows/Rel.v) owns the binary relation carrier, stacks, and
congruence; [RelSPostArr.v](../Arrows/RelSPostArr.v) owns the four SP readings.
Generic normalization (`rel_bind`, `relS_bind`, `relO_*`, `relE_*`) lives in
[RelArrowCoherence.v](../../Classes/RelArrowCoherence.v) and uses the existing
`RelArrow` / `RelArrowChoice` / `RelArrowApply` contracts. `SPostArr.v` specializes
these facts for its canonical relation-reading wrappers.

- [`SPBindOrderCounterexample.v`](SPBindOrderCounterexample.v) refutes ordered
  bind for `StDSP.DSPSt` / `StASLP.ASLPSt` under their global pointwise orders.
  Monad laws and monotonicity in a fixed transformer's precondition still hold.
  Its `dsp_arbitrary_bind_impossible` and `aslp_arbitrary_bind_impossible`
  strengthen this result for Boolean state: any candidate Boolean-to-unit bind
  with the current return and pointwise order cannot satisfy both left identity
  and first-argument monotonicity. The contradiction uses well-formedness of
  the candidate's output, independently of the existing bind.

## Orders and comparisons

ASP's transformer order follows relation inclusion; DSLP reverses it. Their
pointwise orders carry OrderedMonad. DSP/ASLP carry OrderedMonad for recovered
relation inclusion, not their own pointwise reading orders; boolean-state
counterexamples refute that stronger requirement. Orders at a fixed precondition
are distinct from global ones. SPBindOrderCounterexample retains the old
state-only no-go results; SpecificationMonads classifies the old carriers.

BaseGaloisConnections/NewGaloisConnections relate unary presentations;
in-monad SP targets preserve their nonemptiness/precondition side conditions.
SPStBindComparisons studies skew-monadic/functor structure and bind comparisons.
Read the chosen carrier, operations, equality, and order before observations.
