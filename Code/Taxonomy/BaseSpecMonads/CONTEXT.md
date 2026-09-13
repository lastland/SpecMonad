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

Old ASP uses SingletonProg (strict/disjunctive); DSLP uses MSingletonProg
(top-preserving/conjunctive). Old DSP is strict/conjunctive; ASLP is
top-preserving/disjunctive. Nonempty indexed families are intentional.
DSP/ASLP state binds recover relations before composing; do not replace them
with ordinary forward transformer composition. Pure DSPSP/ASLPSP collapse to
ASP/DSLP via property equivalences; reader lifts preserve this per environment.
StASP/StDSLP/StDSP/StASLP supply state-only variants.

## New four-flavour public API

ASPArrowCore/Rel, DSLPArrowCore/Rel, DSPArrowCore/Rel, and ASLPArrowCore/Rel
define binary SPArrT subsets and their own operations/laws. All are monotone;
ASP is strict/disjunctive, DSLP terminating/conjunctive, DSP strict/conjunctive,
ASLP terminating/disjunctive. ASP singleton joins and DSLP accepted-predicate
meets recover relations constructively; DSP/ASLP recovery is classical.
Equalities are transformer iff, not automatically Leibniz bundle equality.
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

## Arrow-derived monad consumers

ASPMonad/DSLPMonad/DSPMonad/ASLPMonad fix input unit and use generic
Classes/ArrowMonad operations/laws. Each exposes pure/state/state-option APIs.
SPure gives a relational carrier, four readings, OrderedMonad_flip, and the
five-operation RelDenote contract; rel_bind/relS_bind/relE_bind describe the
chosen bind through relations. Preserve these APIs alongside property-only
SPostArr; the equivalent bundles are not definitionally the same carrier.

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
