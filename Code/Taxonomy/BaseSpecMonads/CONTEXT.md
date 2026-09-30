# Base specification monads context (main)

Parent: [Taxonomy context](../CONTEXT.md).
Detailed semantics and naming: [Taxonomy README](../README.md).

## Purpose and boundary

These files define specification carriers, operations, healthiness, orders,
and adjunctions without choosing a concrete computation. Effect-specific
interpretations belong to [observations](../EffectObservations/CONTEXT.md).
The imported [TransformerLaws.v](../ComputationMonads/TransformerLaws.v) is
parametric in its base monad despite its directory name.

## Unary specifications

The five presentations associated with *Dijkstra Monads for All* are:

| Source | Carrier and contract |
|---|---|
| [PredMonad.v](PredMonad.v) | `PredM.Pred A = A -> Prop`; also `PredStExc S = stateT S (optionT PredM.Pred)`. |
| [PrePostMonad.v](PrePostMonad.v) | `PPM.PrePost A = Prop * (A -> Prop)`; bind checks continuation preconditions universally and collects results existentially. |
| [SPostMonad.v](SPostMonad.v) | `SPM.SPost` bundles a monotone transformer into `SPM.Over p`, whose propositions imply `p`. |
| [WPureMonad.v](WPureMonad.v) | `WPure` restricts raw `WPureT A = (A -> Prop) -> Prop` by `wpure_mono`; `runWPure` exposes it. |
| [RelPrePostMonad.v](RelPrePostMonad.v) | `RPPM.RelPrePost` uses `Assuming p`, propositions `q` satisfying `q <-> (p -> q)`, and Hoare-order monotonicity. |

Their `Eq1` contracts compare underlying propositions by iff. They are not
the binary carriers of [Arrows](../Arrows/CONTEXT.md) with an input fixed.
`WSt S = stateT S WPure`; `WStExc S = stateT S (optionT WPure)` additionally
supports exceptions. Preserve the subset proofs rather than treating `WPure`
as the raw continuation type used by `WPArr`.

## SP carriers and healthiness

[SPPredicateTransformers.v](SPPredicateTransformers.v) defines raw carriers:
`SPPure A = Prop -> A -> Prop`, `@SPSt S A = (S -> Prop) -> (A * S) -> Prop`,
and `@SPStExc S A = (S -> Prop) -> option (A * S) -> Prop`. The `@` exposes
implicit `S`; the stateful carriers take a shared precondition, not one per state.

The healthiness-carved presentation lives in `OldMonads/`; every current
client in this tree still imports it from there. The files of the same
names directly in this directory are the arrow presentation described in
[SP arrows](#sp-arrows) below, and their names (`ASPStExc`, `retASP`,
`ordASPStExc`, &c.) collide with these, so import only one of the two
unqualified.

| Source | Option-indexed monad | Carrier condition |
|---|---|---|
| [OldMonads/ASPMonad.v](OldMonads/ASPMonad.v) | `ASPStExc` | `SingletonProg`, equivalent to strictness plus disjunctivity. |
| [OldMonads/DSLPMonad.v](OldMonads/DSLPMonad.v) | `DSLPStExc` | `MSingletonProg`, equivalent to top preservation plus conjunctivity. |
| [OldMonads/DSPMonad.v](OldMonads/DSPMonad.v) | `DSPStExc` | `StrictProg` and `ConjunctiveProg`. |
| [OldMonads/ASLPMonad.v](OldMonads/ASLPMonad.v) | `ASLPStExc` | `TerminatingProg` and `DisjunctiveProg`. |

`Terminating` / `TerminatingProg` mean top preservation, not termination of a
computation. Conjunctivity and disjunctivity here quantify over **nonempty**
indexed families; strictness and top preservation supply the empty cases.
`StTrans`, `StASP`, `StDSLP`, `StDSP`, and `StASLP` contain state-only variants.

DSP/ASLP binds recover relations before composing them. `dsp_recov` probes at
the full precondition and a co-singleton; `aslp_recov` probes at the empty
precondition and a singleton. `dsp_carrier` / `aslp_carrier` connect recovery
to healthiness. Do not replace these binds with simple forward composition.
Pure `DSPSP` / `ASLPSP` instead transport the `ASPSP` / `DSLPSP` structures via
`strict_conj_iff_singleton` / `term_disj_iff_msingleton`. The `ASPRd`, `DSLPRd`,
`DSPRd`, and `ASLPRd` reader lifts inherit that collapse environment by environment.

## Orders and adjunctions

- `WP_le` in `WPureMonad.v` and `MR_le` in
  [BaseGaloisConnections.v](BaseGaloisConnections.v) use reverse implication.
  `ordWSt` / `ordWStExc` use forward implication, not lifts of `WP_le`.
- Each SP monad owns its global pointwise order and its `At` order at one
  precondition, such as `ordASPStExc` / `ordASPStExcAt`. The stateful DSP and
  ASLP monads also own a recovered-relation order, such as `ordDSPStExcRel`.
- `BaseGaloisConnections.v` relates the five unary monads.
  [NewGaloisConnections.v](NewGaloisConnections.v) adds `wp_pp_over_adjunction`
  and SP triple targets, including `StSP` and `PureSP` variants. ASP `Under`
  and DSLP `Over` in-monad characterizations use `At` orders with nonemptiness
  conditions; raw `pp2_over` / `pp2_under` are not healthy targets.
- [SPBindOrderCounterexample.v](SPBindOrderCounterexample.v) refutes ordered
  bind for `StDSP.DSPSt` and `StASLP.ASLPSt` under their existing global orders.
  This does not refute monad laws or monotonicity in the precondition.
- [SpecificationMonads.v](SpecificationMonads.v) checks every monad here
  against `OrderedMonad` under its own order. All pass except `DSPStExc`,
  `ASLPStExc`, `StDSP.DSPSt`, and `StASLP.ASLPSt`, refuted at `S = bool`;
  those four are ordered under inclusion of the recovered relation
  (`ordDSPStExcRel` &c.). `PredStExc` is checked under `ordPredStExc`
  from `PredMonad.v`.

## SP arrows

The arrow presentation builds each SP monad as a Hughes arrow with the input
fixed at `unit`, on the arrows of [SPostArr.v](../Arrows/SPostArr.v) and the
`stateArrT` / `optionArrT` transformers of [Classes](../../Classes/CONTEXT.md).
Their `ret` / `bind` are `ret_arrow` / `bind_arrow`, and `MonadLawsE` is
`MonadLawsE_Arrow`, so no monad law is proved per flavour. Each carrier is
`SPArrT` of [SPArr.v](../Arrows/SPArr.v) refined by homomorphism properties:
all four are monotone, and the table lists the rest. The operations are each
flavour's own, not inherited from `SPArrT`.

| Flavour | Files | Carrier and relation |
|---|---|---|
| ASP | [ASPArrowCore.v](ASPArrowCore.v), [ASPArrowRel.v](ASPArrowRel.v), [ASPMonad.v](ASPMonad.v) | `ASPArr`: strict and disjunctive, i.e. join-preserving (`asp_join_iff`); `aspRel` is a bijection with relations. |
| DSLP | [DSLPArrowCore.v](DSLPArrowCore.v), [DSLPArrowRel.v](DSLPArrowRel.v), [DSLPMonad.v](DSLPMonad.v) | `DSLPArr`: top-preserving and conjunctive, i.e. meet-preserving (`dslp_meet_iff`); `dslpRel` reverses inclusion (`dslpRel_incl`). |
| DSP | [DSPArrowCore.v](DSPArrowCore.v), [DSPArrowRel.v](DSPArrowRel.v), [DSPMonad.v](DSPMonad.v) | `DSPArr`: strict and conjunctive, exactly the DSPs of relations (`dsp_hom_iff`, classically); the relation is recovered by a classical probe (`dspRel`). |
| ASLP | [ASLPArrowCore.v](ASLPArrowCore.v), [ASLPArrowRel.v](ASLPArrowRel.v), [ASLPMonad.v](ASLPMonad.v) | `ASLPArr`: top-preserving and disjunctive, exactly the ASLPs of relations (`aslp_hom_iff`, classically); recovered by `aslpRel`. |
| shared | [SPure.v](SPure.v) | relations as the SP carrier, the four readings of one, `OrderedMonad_flip`, and `RelDenote` with `rel_bind` / `relS_bind` / `relE_bind`: `bind` as composition of denoted relations for any arrow whose operations denote the relational ones. |

`ASPMonad.v` and `DSLPMonad.v` each give `ASP`, `ASPSt S`, `ASPStExc S` (resp.
DSLP) an `OrderedMonad` instance for pointwise implication, proved from
`aspRel_incl` / `dslpRel_incl`. `DSPMonad.v` and `ASLPMonad.v` give DSP and
ASLP two orders each at every level: the relational order `ordDSPRel` &c.
(inclusion of the denoted relation) carries the `OrderedMonad` instances,
through `RelDenote_DSP` / `RelDenote_ASLP`; the reading's own order `ordDSP`
&c. does not, and cannot: `not_OrderedMonad_DSPSt` / `not_OrderedMonad_ASLPSt`
refute it at `S = bool` in the first argument of `bind` alone, and
`dsp_order_diverges` shows the two orders differ. Each file also has the
readings at a client precondition (`getDSPSt`, `getDSPStExc`, `getDSPPure`,
and their `_of` forms for elements built from a relation).

## Reading order

Read the raw carrier, its healthiness condition, and its operations before the
law proofs. For SP, follow ASP, DSLP, DSP, then ASLP, in `OldMonads/` for the
healthiness presentation or `*ArrowCore.v` then `*ArrowRel.v` then `*Monad.v`
for the arrow one; for triple embeddings,
read the exact order and side conditions before following an observation client.
