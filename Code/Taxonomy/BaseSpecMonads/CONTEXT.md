# Base specification monads context

Parent: [Taxonomy context](../CONTEXT.md).
Details: [SP monads](../README.md#3-the-sp-specification-monads),
[WP monads](../README.md#4-the-wp-specification-monads), and
[DM4all adjunctions](../README.md#7-the-dm4all-specification-monads-and-their-adjunctions).

## Purpose and scope

This is the unary specification layer: carriers, well-formedness, operations,
laws, orders, and specification-to-specification connections. Its definitions
do not mention a concrete computation monad.

## Established terms and definitions

- [SPPredicateTransformers.v](SPPredicateTransformers.v) defines raw carriers:
  `SPPure A := Prop -> A -> Prop`, `SPSt S A` with outcomes `A * S`, and
  `SPStExc S A` with outcomes `option (A * S)`. The latter two take `S -> Prop`.
- **Well-formedness** selects the SP monads. [`ASPStExc`](ASPMonad.v) uses
  `SingletonProg`, equivalent to strictness plus disjunctivity;
  [`DSLPStExc`](DSLPMonad.v) uses `MSingletonProg`, equivalent to termination
  plus conjunctivity. [`DSPStExc`](DSPMonad.v) is strict conjunctive;
  [`ASLPStExc`](ASLPMonad.v) is terminating disjunctive.
- [`DSPDivExc` / `ASLPDivExc`](DivExcSP.v) stack two `optionT` layers over
  pure `DSPSP` / `ASLPSP`. Their runners take `Prop` preconditions and
  `option (option A)` outcomes; the full-outcome observation assigns separate
  indices to successful return, exception, and divergence. `bindDSP_mono` /
  `bindASLP_mono` prove pure bind monotonicity in both arguments;
  `bindDSPDivExc_mono` / `bindASLPDivExc_mono` lift it through both layers.
- [`WPureT` / `WPure`](WPureMonad.v) distinguish the raw WP transformer
  from its monotone subset. `WSt` and `WStExc` stack state and optional
  exceptions over `WPure`; `runWPure` exposes application.
- [`NewGaloisConnections.v`](NewGaloisConnections.v) supplies `Over`/`Under`
  targets and generic triple characterizations. Its `StSP` and `PureSP`
  modules adapt these to state-only and pure outcomes.

## Dependency boundaries

- Dependencies are specification modules, libraries, and logical principles.
  [TransformerLaws.v](../ComputationMonads/TransformerLaws.v) is shared generic
  infrastructure despite its location: importing it introduces no concrete
  computation dependency.
- [Observations](../EffectObservations/CONTEXT.md) instantiate these carriers
  with computation semantics. [Arrows](../Arrows/CONTEXT.md) provide a separate
  binary presentation; `WPArr` deliberately uses raw `WPureT`.
- [BaseGaloisConnections.v](BaseGaloisConnections.v) relates the DM4all monads;
  `NewGaloisConnections.v` builds further WP and SP embeddings on that layer.

## Recovery proof ownership

[DSPMonad.v](DSPMonad.v) and [ASLPMonad.v](ASLPMonad.v) each share local,
outcome-generic recovery and congruence proofs between their option-outcome and
`StDSP` / `StASLP` presentations. Callers use the specialized `dsp_recov` /
`aslp_recov` and `dsp_cong` / `aslp_cong` lemmas; the generic helpers are
implementation details.

`dsp_comp_recov_option` and `aslp_comp_recov_option` eliminate recovery from
option-outcome relational composition. They reuse `comp_cong` and recovery;
observation proofs lift the resulting equivalence with specialized congruence
and combine it with `bindDSPProg_dsp` / `bindASLPProg_aslp`. Pair-outcome clients
use `StDSP.comp_cong` and their specialized recovery lemmas directly.

## Semantic traps

- Raw SP carriers alone do not supply the four monads. `Terminating` means
  top preservation; conjunctivity/disjunctivity quantify over nonempty families.
- An option outcome does not itself prescribe exception or divergence semantics.
  That choice belongs to the observation, not the well-formedness predicate.
- Stateful DSP/ASLP bind recovers and composes relations before re-reading them.
  See `dsp_recov` / `aslp_recov`; a simple forward pass is insufficient.
- [`SPBindOrderCounterexample.v`](SPBindOrderCounterexample.v) refutes ordered
  bind for `StDSP.DSPSt` / `StASLP.ASLPSt` under their global pointwise orders.
  Monad laws and monotonicity in a fixed transformer's precondition still hold.
  Its `dsp_arbitrary_bind_impossible` and `aslp_arbitrary_bind_impossible`
  strengthen this result for Boolean state: any candidate Boolean-to-unit bind
  with the current return and pointwise order cannot satisfy both left identity
  and first-argument monotonicity. The contradiction uses well-formedness of
  the candidate's output, independently of the existing bind.
- `WP_le` is reverse implication; `ordWSt` / `ordWStExc` are forward implication.
  Global SP orders and `...At` orders at one precondition are also distinct.
- Pure DSP collapses to ASP, and pure ASLP to DSLP. Reader variants lift these
  pure carriers pointwise; a shared set-of-environments precondition would
  couple environments and is not the existing reader carrier.

## Reading order

For SP, read the raw properties, then `ASPMonad.v`, `DSLPMonad.v`,
`DSPMonad.v`, and `ASLPMonad.v`; each carries its `St*` slice and pure/reader
variants. For WP, start with `WPureMonad.v`. Continue to the Galois files for
targets and orders, then the [SP](../EffectObservations/SP/CONTEXT.md) or
[WP observations](../EffectObservations/WP/CONTEXT.md) that consume them.
