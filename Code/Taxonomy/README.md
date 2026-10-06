# Taxonomy

This directory is the core of the project. It defines a family of computation
monads, several families of specification monads, and *observations* connecting
them.

The organising principle is a dependency boundary:

> **Specification carriers do not depend on concrete computation monads.**
> Observations connect the two sides by interpreting computation outcomes.

`BaseSpecMonads/` and `Arrows/` use specification types, generic infrastructure,
and library definitions. The generic `TransformerLaws.v` happens to live under
`ComputationMonads/`, but names no concrete computation monad. Concrete models
live in `ComputationMonads/`; their observations, triples, and comparisons live
in `EffectObservations/`. Shared program definitions live in `ExampleProgramDefs.v`.

A second separation runs alongside it: **defining** an observation and
**comparing** observations live in different files. `EffectObservations/WP/` and
`EffectObservations/SP/` define observations and local results;
`EffectObservations/Taxonomy_*.v` assemble the cross-observation taxonomy.

Start with the computation table (§2), then choose a specification presentation
(§3–4 and §8) and its observations (§5). The [context map](../../CONTEXT-MAP.md)
provides shorter directory guides. Formulas below describe carriers and readings;
unless shown as complete declarations, they are schematic rather than standalone
Coq commands.

---

## 1. Directory layout

```
Taxonomy/
  ComputationMonads/     TransformerLaws            -- generic optionT/stateT/readerT laws
                         StDivITree, StExcNonDet, StDivNonDet, StDivExcNonDet,
                         DivNonDet, DivExcNonDet, RdDivNonDet
  BaseSpecMonads/        PredMonad, PrePostMonad, SPostMonad, WPureMonad,
                         RelPrePostMonad             -- the five DM4all monads
                         SPPredicateTransformers     -- earlier raw SP carriers + healthiness
                         ASPMonad, DSLPMonad, DSPMonad, ASLPMonad
                         *ArrowCore, *ArrowRel, SPure -- canonical SP arrows and readings
                         DivExcSP, SpecificationMonads, SPStBindComparisons
                         BaseGaloisConnections, NewGaloisConnections
      OldMonads/         ASPMonad, DSLPMonad, DSPMonad, ASLPMonad -- earlier SP carriers
  Arrows/                Rel, PrePostArr, RelPrePostArr, WPArr, GaloisArr
                         SPArr, PredicateTransformerProperties -- SP healthiness conditions
                         SPostArr                    -- canonical ASP/DSLP compatibility API
                         RelSPostArr                 -- ASP/DSLP readings of Rel
                         SPostArrMonad               -- monad dictionaries and SP readings
                         SPostArrEquiv               -- equivalence and transformer lifts
                         OptionLoop                  -- obstruction to option feedback
     Examples/           SPostArrExamples             -- checked clients
     Tests/              ArrowMonadInstances          -- concrete monad dictionaries
                         ArrowTransformerInstances    -- transformer resolution checks
  EffectObservations/
      WP/                StDivITree_WStExc, StExcNonDet_WStExc,
                         StDivExcNonDet_WStExc, StDivNonDet_WSt
      SP/                StDivExcNonDet_SPStExc, StDivNonDet_SPStExc,
                         StDivNonDet_SPSt, DivNonDet_SPPure,
                         RdDivNonDet_RdSPPure, DivExcNonDet_SPDivExc
                         SPostArrObservation         -- shared SP judgments
                         StDivITree_SPostArr, StExcNonDet_SPostArr,
                         StDivNonDet_SPostArr, StDivExcNonDet_SPostArr
      (root)             Taxonomy_StDivExcNonDet_StExc,
                         Taxonomy_StDivNonDet_StExc, Taxonomy_StDivNonDet_St
  DijkstraMonads/        Dijkstra_StDivExcNonDet_WStExc,
                         Dijkstra_StDivExcNonDet_SPStExc, Dijkstra_StDivNonDet_SPSt
  OldSP/                 the earlier reading-based SP presentation
  deprecated/            older iterations, excluded from the build
  (root)                 ExampleProgramDefs, InCorrectnessPrinciples
```

Computation-specific observation files are named
`<computation monad>_<specification target>.v`; one file can define several
readings of that source. Logical paths follow
the directories: `Incorrectness.Taxonomy.BaseSpecMonads.WPureMonad`,
`Incorrectness.Taxonomy.EffectObservations.SP.StDivExcNonDet_SPStExc`, and so
on.

## 2. Computation monads

| Type | Definition | File | Effects |
|---|---|---|---|
| `stdivitree S A` | `stateT S (optionT (itree void1)) A` | `ComputationMonads/StDivITree.v` | state, exceptions, divergence (deterministic) |
| `stexcnd S A` | `stateT S (optionT SetM) A` | `ComputationMonads/StExcNonDet.v` | state, nondeterminism, **exceptions** |
| `stdivnd S A` | `stateT S (optionT SetM) A` | `ComputationMonads/StDivNonDet.v` | state, nondeterminism, **divergence** |
| `stdivexcnd S A` | `stateT S (optionT (optionT SetM)) A` | `ComputationMonads/StDivExcNonDet.v` | state, nondeterminism, exceptions **and** divergence |
| `divnd A` | `optionT SetM A` | `ComputationMonads/DivNonDet.v` | nondeterminism, **divergence** (no state) |
| `divexcnd A` | `optionT (optionT SetM) A` | `ComputationMonads/DivExcNonDet.v` | nondeterminism, exceptions **and explicit divergence** (no state) |
| `rddivnd R A` | `readerT R divnd A` | `ComputationMonads/RdDivNonDet.v` | environment, nondeterminism, **divergence** |

`stexcnd` and `stdivnd` share a carrier and differ only in the *reading* of the
distinguished outcome `None`: an exception in the first, divergence in the
second. Nothing in the type distinguishes them; what fixes the meaning is which
operations are offered. `StExcNonDet.v` supplies `MonadExc` (`raiseP`/`catchP`);
`StDivNonDet.v` deliberately supplies none, and offers `divergeD`, `mayDiverge`
and `orD` instead. `None` is absorbing under `bind` in both models, so the same
monad structure supports either interpretation. The distinction is semantic,
not enforced by different raw carriers.

`StDivNonDet.v` also carries `stdivndNE`, the non-empty fragment used by the
`WSt` observations. Non-emptiness supports `obsDWP_strict`, `obsAWLP_top`, and
taxonomy inclusions; the observations' postcondition-monotonicity proofs do
not use it. See [the WP context](EffectObservations/WP/CONTEXT.md).

`divnd` is the state-free base: `stdivnd S A` and `stateT S divnd A` are
definitionally equal. It supplies `divergeD`, `orD`, `mayDiverge`, a non-empty
fragment `divndNE`, and pointwise outcome laws such as `outcomes_bind` and
`diverge_absorbing`.

`rddivnd` puts a read-only environment on that base instead of a state. The two
have the same shape but differ in the outcome:

```coq
stdivnd R A  =  R -> option (A * R) -> Prop     (* state: the outcome carries R *)
rddivnd R A  =  R -> option  A      -> Prop     (* reader: it does not          *)
```

so `RdDivNonDet.v` offers `MonadReader` (`ask`, `local`) where `StDivNonDet.v`
offers `MonadState` (`get`, `put`), and `nonEmpty_localD` is the extra closure
lemma the non-empty fragment needs.

`stdivexcnd` distinguishes exceptions from divergence with two option layers:
`Some (Some (a, s'))` is a normal return, `Some None` an exception, and raw
`None` divergence. The deterministic `stdivitree` also distinguishes these
effects: `Ret None` is an exception, while divergence belongs to the underlying
ITree rather than to its option result.

`TransformerLaws.v` lifts `Eq1`, equivalence, and monad laws through `optionT`,
`stateT`, and `readerT`. Both computation and specification stacks reuse these
instances; their hypotheses concern only the base monad's operations and laws.

### Raw outcome laws

**Computation modules own the raw outcome-law interface.** The stateful
nondeterministic laws are constructive pointwise `<->` statements about full
outcome sets at an initial state and raw outcome:

- [StExcNonDet.v](ComputationMonads/StExcNonDet.v) owns `outcomes_ret` /
  `outcomes_bind` for the shared single-option dictionaries, plus get/put/raise
  laws. Both `stexcnd` and `stdivnd` use those return/bind operations by
  definitional conversion.
- [StDivNonDet.v](ComputationMonads/StDivNonDet.v) owns `outcomes_diverge`:
  `divergeD` has exactly the outcome `None`.
- [StDivExcNonDet.v](ComputationMonads/StDivExcNonDet.v) owns the double-option
  return/bind laws and full laws for get, put, raise, `pickP`, and `spinP`.

Bind runs the continuation only after a normal return and propagates exception
or divergence tokens unchanged. An empty prefix blocks, but an empty
continuation does not erase a preceding exception or divergence. `pickP` at
`Empty_set` blocks: it has no outcome, not even divergence.

SP/WP clients reuse this interface rather than independently normalizing the
raw transformer stacks. Observation modules retain derived slice and
non-empty-carrier adapters; those adapters choose the retained outcomes or
project through `getNE`. This seam leaves specification-side recovery in the
SP monad modules (§3). See the [computation context](ComputationMonads/CONTEXT.md#raw-outcome-law-interface)
for the law inventory.

## 3. The SP specification monads

> The four files named below now live in `BaseSpecMonads/OldMonads/`, and
> the earlier healthy-carrier clients import them from there. The files of the same
> names directly in `BaseSpecMonads/` are the arrow presentation
> (`*ArrowCore.v`, `*ArrowRel.v`, `*Monad.v`, `SPure.v`),
> described in `BaseSpecMonads/CONTEXT.md`; the two sets of names collide,
> so import only one unqualified.

Four healthiness conditions select the SP monads from the raw transformer
type `(S -> Prop) -> Outcome -> Prop`. The raw type alone does not justify the
sequencing laws: `SPostMonad.v` contains a counterexample to associativity for
the weaker stateful Kenji-style carrier and its proposed bind.

| Monad | Carrier condition | Equivalent healthiness conditions | Reading of a relation `R` |
|---|---|---|---|
| `ASPStExc` | `SingletonProg` | strict, universally disjunctive | `∃s ∈ pre, R s r` (angelic) |
| `DSLPStExc` | `MSingletonProg` | terminating, universally conjunctive | `∀s, R s r → pre s` (demonic, liberal) |
| `DSPStExc` | `StrictProg ∧ ConjunctiveProg` | **strict conjunctive** | `R⁻¹(r) ≠ ∅ ∧ R⁻¹(r) ⊆ pre` |
| `ASLPStExc` | `TerminatingProg ∧ DisjunctiveProg` | **terminating disjunctive** | `R⁻¹(r) = ∅ ∨ pre ∩ R⁻¹(r) ≠ ∅` |

The carriers live in `SPPredicateTransformers.v`, named to match
`WPureMonad.v`'s stacks:

```coq
SPPure  A     := Prop -> A -> Prop
SPSt    S A   := (S -> Prop) -> (A * S) -> Prop          (* terminating slice *)
SPStExc S A   := (S -> Prop) -> option (A * S) -> Prop   (* with the extra outcome *)
```

`Arguments SPSt {_}` / `Arguments SPStExc {_}` keep `S` implicit.

One file per monad, in dependency order:

```
SPPredicateTransformers.v   the three carriers + Strict/Terminating/
                            Conjunctive/Disjunctive and their Prog variants
SPostMonad.v                the DM4all SPost monad + both Kenji developments
ASPMonad.v                  SingletonProg,  ASPStExc
DSLPMonad.v                 MSingletonProg, DSLPStExc
DSPMonad.v                  DSPStExc        (needs ASP and DSLP)
ASLPMonad.v                 ASLPStExc       (needs ASP, DSLP, and DSPMonad's
                                              comp_cong)
```

Each monad comes with `ret`, `bind`, `Monad`, `Eq1`, `Eq1Equivalence` and
`MonadLawsE` (all four laws), plus **its own refinement order and
monotonicity in the precondition** — `ordASPStExc` / `ordASPStExcAt` /
`asp_bot` / `aspMono` in `ASPMonad.v`, and correspondingly for the other three.
The raw order `ordSPStExc` sits with the carriers.

`retDSPStExc`/`bindDSPStExc` are the conjunction of the ASP and DSLP parts;
`retASLPStExc`/`bindASLPStExc` the disjunction — see `dsp_split` / `aslp_split`
and the `aspPart*` / `dslpPart*` projections.

**Stateful DSP and ASLP recover relations before sequencing.** The `aspPart*`
and `dslpPart*` projections read each argument's recovered relation. DSP recovers
`R s r` by probing at top and the co-singleton `fun t => t <> s`; ASLP probes
at bottom and the singleton `fun t => t = s`. The `dsp_recov` and `aslp_recov`
lemmas justify these probes. The binds compose the recovered relations and
read the result again. The `dsp_carrier` and `aslp_carrier` lemmas connect this
representation to the stated healthiness conditions.

**Ordered bind is a separate requirement.**
[`SPBindOrderCounterexample.v`](BaseSpecMonads/SPBindOrderCounterexample.v)
proves that the state-only `StDSP.DSPSt` and `StASLP.ASLPSt` binds do not
preserve their global pointwise implication orders, even with the same
continuation on both sides. The Boolean-state example uses the existing
directly defined binds: one command returns only from `false`, another preserves
both states, and their common continuation resets the state to `false`. The
resulting nonmonotonicity blocks an `OrderedMonad` instance using these binds
and orders together, as required by the standard Dijkstra bind construction.
Their `MonadLawsE` instances and `dspMono` / `aslpMono` precondition-monotonicity
lemmas remain valid; the counterexample does not depend on arrow-derived bind.

### The terminating slice lives alongside each monad

The same four monads over `A * S` instead of `option (A * S)` are factored
exactly like the option-outcome ones, each piece in the file for its monad, in a
module of its own:

| file | option outcome (top level) | terminating slice |
|---|---|---|
| `SPPredicateTransformers.v` | `Strict`/`Terminating`/`Conjunctive`/`Disjunctive` (+`Prog`) | `Module StTrans` |
| `SPostMonad.v` | `KenjiProgSP` | `Module StKenji` |
| `ASPMonad.v` | `ASPStExc` | `Module StASP` |
| `DSLPMonad.v` | `DSLPStExc` | `Module StDSLP` |
| `DSPMonad.v` | `DSPStExc` | `Module StDSP` |
| `ASLPMonad.v` | `ASLPStExc` | `Module StASLP` |

Each module imports its predecessors (`StDSP` opens `StTrans StASP StDSLP`, for
example). Module qualification distinguishes the parallel names in the two
outcome indexings.

### The pure variants, and why DSP and ASLP collapse there

Each monad also has a state-free variant over `SPPure A = Prop -> A -> Prop`:
`ASPSP` / `DSLPSP` in their own files, and `DSPSP` / `ASLPSP` in
`Section PureDSPMonad` / `Section PureASLPMonad`. All four have `Monad`,
`Eq1`, `MonadLawsE` and their orders (`ordASPSP` / `ordASPSPAt`, &c.).

But the last two are **not new monads**. At `SPPure` the precondition is a
`Prop`, and:

```coq
strict_conj_iff_singleton   : Strict w /\ Conjunctive w   <-> Singleton w    (* DSP  = ASP  *)
term_disj_iff_msingleton    : Terminating w /\ Disjunctive w <-> MSingleton w (* ASLP = DSLP *)
```

`strict_to_singleton` shows that pure strictness already implies `Singleton`;
the dual `terminating_to_msingleton` gives the multiplicative case. Thus
`DSPSP` presents the same subset as `ASPSP`, while `ASLPSP` presents the same
subset as `DSLPSP`. Their operations are transported through `asp_to_dsp` /
`dsp_to_asp` and `dslp_to_aslp` / `aslp_to_dslp`, respectively. These maps leave
the underlying transformer unchanged.

The pure precondition is one proposition, not a set of independently chosen
initial states. For an inhabited inverse image, requiring every predecessor
to satisfy that proposition is equivalent to requiring some predecessor to do
so. This is why DSP collapses to ASP and ASLP to DSLP in the pure observation.

The pure binds are monotone in both arguments: `bindDSP_mono` and
`bindASLP_mono` transport a refinement of the prefix and a pointwise refinement
of the continuation to a refinement of the composite.

[`DivExcSP.v`](BaseSpecMonads/DivExcSP.v) lifts these carriers through two
`optionT` layers, yielding `DSPDivExc` and `ASLPDivExc`. The precondition remains
`Prop`; only the outcome type changes to `option (option A)`.
`bindDSPDivExc_mono` and `bindASLPDivExc_mono` lift the pure monotonicity results
twice using `TransformerLaws.bind_optionT_mono`. Their monad laws also follow
from the existing transformer laws.

The [full-outcome observation](EffectObservations/SP/DivExcNonDet_SPDivExc.v)
preserves return and bind from stateless `divexcnd`, retaining successful
returns (`Some (Some a)`), exceptions (`Some None`), and divergence (`None`).
DSP reads `p /\ outcomes m o`; ASLP reads `p \/ ~ outcomes m o`. Thus DSP at
`True` expresses reachability, while ASLP at `False` expresses unreachability.
The checked `mixed_DSP_outcomes` and `mixed_ASLP_outcomes` examples show a
nondeterministic choice between returning `0`, raising, and diverging.

### The reader-indexed variants

Each SP monad file also defines `readerT R` over its pure variant, next to the
pure one:

```coq
ASPRd R A := readerT R ASPSP  A      (* ASPMonad.v,  Section RdASPMonad  *)
DSLPRd R A := readerT R DSLPSP A     (* DSLPMonad.v, Section RdDSLPMonad *)
DSPRd R A := readerT R DSPSP  A      (* DSPMonad.v,  Section RdDSPMonad  *)
ASLPRd R A := readerT R ASLPSP A     (* ASLPMonad.v, Section RdASLPMonad *)
```

with `get*Rd w r`, `Monad__*Rd`, `Eq1__*Rd`, `MonadLawsE__*Rd` (from the
generic `readerT` instances) and the orders `ord*Rd` / `ord*RdAt`.

The precondition slot stays a bare `Prop`, so this is the **pointwise** lift:
one `Prop` per environment, environments specified independently. Since every
fibre is additive, an `ASPRd R A` is exactly a relation `R -> A -> Prop`
(`getASPRd_singleton`).

The reader lift inherits the pure collapse: `DSPRd` does not retain a distinct
DSP reading, nor `ASLPRd` a distinct ASLP reading. A transformer with a shared
precondition `(R -> Prop) -> A -> Prop` can express a different requirement.
For example, with `R = bool` and an inhabited output type,
`fun pre _ => forall r : bool, pre r` is strict and conjunctive but is not
determined by singleton preconditions. This illustrates a distinction in
precondition shape; the current reader observations use only the pointwise lift.

### In-monad characterizations

`NewGaloisConnections.v` supplies the following in-monad characterizations.
ASP `Over` and DSLP `Under` use global orders; the other two supplied targets
use orders at one precondition:

| | `Over` | `Under` |
|---|---|---|
| ASP | `ordASPStExc obs (pp2asp_over …)` — global | `ordASPStExcAt pre (pp2asp_under …) obs` — needs `∃s, pre s` |
| DSLP | `ordDSLPStExcAt pre obs (pp2dslp_over …)` — needs `∃s, ¬pre s` | `ordDSLPStExc (pp2dslp_under …) obs` — global |
| DSP / ASLP | not supplied | not supplied |

`Over` always compares `obs ⊑ target`, `Under` always `target ⊑ obs`. The two
side conditions are forced by the healthiness conditions themselves (`asp_bot`:
every ASP is `False` at `⊥`; `dslp_top`: every DSLP is `True` at `⊤`) and are
not removable for these targets. These statements concern targets inside the
well-formed monads. Comparisons against the raw `pp2_over` / `pp2_under`
transformers are separate characterizations and do not require these two side
conditions.

## 4. The WP specification monads

`BaseSpecMonads/WPureMonad.v` holds exactly three developments plus their
orders:

```coq
WPureT A   := (A -> Prop) -> Prop                    (* raw; used by Arrows/WPArr.v *)
wpure_mono f := forall p q, (p ⊆ q) -> f p -> f q
WPure  A   := { f : WPureT A | wpure_mono f }        (* the monad *)

WSt    S   := stateT S WPure                          (* W^St     *)
WStExc S   := stateT S (optionT WPure)                (* W^StExc  *)
```

After applying the stack runners and `runWPure`, `WSt` takes an initial state
and a postcondition on `A * S`. `WStExc` instead takes a postcondition on
`option (A * S)` and supplies `MonadExc`. These are the shapes of the
evaluators, not equalities of the bundled carriers with unrestricted functions.

`ret`, `bind`, `Eq1` (pointwise iff) and `MonadLawsE` are proved directly for
`WPure`; both stacks get their laws from the `Eq1`-generic `optionT` / `stateT`
instances in `ComputationMonads/TransformerLaws.v`.
`Coercion runWPure : WPure >-> Funclass` keeps application (`w post`) working
through the subset type.

The adjunction and `Proper_bind` proofs use the bundled monotonicity. Each WP
observation therefore supplies an `obs*_mono` proof when constructing a
`WPure` value. Downstream proofs can use these lemmas or the public unfolding
lemmas without unpacking the subset type.

All three WP orders live in `WPureMonad.v`, each next to the type it orders —
matching the SP side:

| order | on | direction |
|---|---|---|
| `WP_le` (+ `WP_le_PreOrder`) | `WPure` | **reverse**: `forall k, w2 k -> w1 k` (DM4all; a weaker precondition is lower) |
| `ordWSt` | `WSt S` | forward: `forall s post, w1 s post -> w2 s post` |
| `ordWStExc` | `WStExc S` | forward |

The direction mismatch is deliberate and visible in one file. The DM4all
adjunctions are stated against the reverse `WP_le`; the triple characterisations
in `EffectObservations/` use the forward stack orders. They are opposite
conventions, not a lifting of one another — lifting `WP_le` through the
transformers would give `forall s, m2 s ⊆ m1 s`.

**`Arrows/WPArr.v` uses the raw carrier `WPureT`**, not `WPure`. Its `ArrowEq`
is Leibniz equality. Some laws hold by conversion; laws involving products and
sums also use functional extensionality. This equality contract differs from
`WPure`'s pointwise logical equivalence.

## 5. Observations

An observation maps computations into a specification carrier. Preservation
theorems relate its source and target return/bind operations. For stateful
nondeterministic sources, they combine computation-owned outcome laws (or
derived adapters) with specification-side laws. Arrow clients use shared arrow
normalization on the target side. Defining a reading alone does not establish
these morphism laws.

Triples use either the base-monad judgments or the shared arrow judgments
described below. Their refinement characterizations and the comparisons in §6
also depend on the chosen orders and, where stated, side conditions.

### WP side — `EffectObservations/WP/`

| File | Source | Target | Observations | Local return/bind laws | Module |
|---|---|---|---|---|---|
| `StDivITree_WStExc.v` | `stdivitree` | `WStExc` | all four | not proved here | — |
| `StExcNonDet_WStExc.v` | `stexcnd` | `WStExc` | `obsDWP`, `obsAWP` only | not proved here | — |
| `StDivExcNonDet_WStExc.v` | `stdivexcnd` | `WStExc` | all four | proved | — |
| `StDivNonDet_WSt.v` | `stdivndNE` | `WSt` | all four | proved | `TermSliceObsWP` |

The four readings are `obsDWP` (demonic total), `obsDWLP` (demonic liberal),
`obsAWP` (angelic total), `obsAWLP` (angelic liberal). `StExcNonDet_WStExc.v`
supplies no distinct liberal readings: its source has exceptions but no separate
divergence outcome. `StDivITree_WStExc.v` proves the deterministic
angelic–demonic collapse in `obsWPCollapse` / `obsWLPCollapse`.

The four double-option return laws compare the observed return with
`WPureMonad.retP S a`, where state `S` and result `A` are independent. The
earlier `retP A a` statement restricted them to the same type; the
[audit](../Checks/Assumptions.v) now includes `Check` instantiations with `bool`
state and `0 : nat`.

`StDivNonDet_WSt.v` targets `WSt`, whose postconditions range over `A * S`, so
divergence is visible to the *observation* but not to the *postcondition*: the
total/liberal axis is carried by the choice of observation. Its non-empty source
`stdivndNE` supports `obsDWP_strict`, `obsAWLP_top`, and selected taxonomy
inclusions. Postcondition monotonicity alone does not require non-emptiness.
Its `TermSliceObsWP.outcomes_bind` derives from `StExcNonDet.outcomes_bind`
through `getNE`; the non-empty carrier does not need another raw bind proof.

### SP side — `EffectObservations/SP/`

| File | Source | Target | Divergence visible in specs? | Module |
|---|---|---|---|---|
| `StDivExcNonDet_SPStExc.v` | `stdivexcnd` | `SPStExc` | **no** — reads the terminating slice | — |
| `StDivNonDet_SPStExc.v` | `stdivnd` | `SPStExc` | **yes** — `None` is an ordinary outcome | `FullOutcomeObs` |
| `StDivNonDet_SPSt.v` | `stdivnd` | `SPSt` | **no** — reads the terminating slice | `TermSliceObs` |
| `DivNonDet_SPPure.v` | `divnd` | `SPPure` | **no** — reads the terminating slice | `PureObs` |
| `DivExcNonDet_SPDivExc.v` | `divexcnd` | `DSPDivExc` / `ASLPDivExc` | **yes** — retains both failure tokens | — |
| `RdDivNonDet_RdSPPure.v` | `rddivnd` | `ASPRd` / `DSLPRd` / `DSPRd` / `ASLPRd` | **no** — reads the terminating slice | `RdPureObs` |

Each row supplies well-formed observations and their return/bind laws.
`DivExcNonDet_SPDivExc.v` supplies DSP and ASLP; the other rows supply all four
readings. The first four rows name the raw outcome indexing; their actual
targets are the corresponding ASP, DSLP, DSP, and ASLP subsets. Note the
contrast in divergence visibility:

- `StDivExcNonDet_SPStExc.v` reads
  `unOptionT (unOptionT (runStateT m s)) (Some r)`; the outer `Some` discards
  the divergent outcome, so its transformers see exceptions but **not**
  divergence.
- `StDivNonDet_SPStExc.v` keeps `None` in the outcome type, so
  `getASPStExc (obsASP m) pre None` asserts *"some `pre`-state may diverge"* and
  `getDSLPStExc (obsDSLP m) pre None` *"every state that may diverge satisfies
  `pre`"*.
- `StDivNonDet_SPSt.v` observes the same monad into the `A * S`-indexed spec
  monads, so divergence is projected away again: `divergeD` satisfies every
  ASP `Over` triple vacuously. Its DSLP reading, by contrast, is always true.
- `DivExcNonDet_SPDivExc.v` retains every raw outcome of stateless `divexcnd`:
  `Some (Some a)` for return, `Some None` for exception, and `None` for
  divergence. Its double-option specification binds preserve pointwise order.

The two modules exist because `StDivNonDet_SPStExc.v` and `StDivNonDet_SPSt.v`
observe the same computation monad into differently-indexed targets, so their
`obsASP` and friends would otherwise clash.

`StDivNonDet_SPStExc.v` imports computation and specification modules, but no
sibling observation file. That is the intended shape for a new observation.

`FullOutcomeObs` uses the shared `StExcNonDet.outcomes_ret` / `outcomes_bind`
directly. `TermSliceObs` derives its return/bind and absence-of-divergence
facts by selecting `Some r` from the full raw laws. The stateful double-option
observation in `StDivExcNonDet_SPStExc.v` similarly uses `StDivExcNonDet` laws
at `Some r`, retaining the inner exception outcome while omitting outer
divergence. The stateless `DivExcNonDet_SPDivExc.v` instead uses
`DivExcNonDet` laws at every raw outcome, retaining both failure tokens.

`RdDivNonDet_RdSPPure.v` threads the reader through the observation rather than
absorbing it: the target is the *same* transformer applied to the specification
side, `readerT R divnd A --> ASPRd R A = readerT R ASPSP A`, so each of its
laws is the corresponding `PureObs` law read at one environment. The four
targets `ASPRd` / `DSLPRd` / `DSPRd` / `ASLPRd` are defined in the SP monad
files themselves (§3). Its triples take `pre : R -> Prop` and are read
pointwise in the environment.

These reader observations do not use a shared set-of-environments precondition
of shape `(R -> Prop) -> A -> Prop`; see the distinction in §3. No alternative
reader observation is defined here.

`DivNonDet_SPPure.v` is the state-free case of `StDivNonDet_SPSt.v`: stripping
`S` collapses every `S -> Prop` precondition to a single `Prop`, the
existential `exists s, pre s /\ _` to `pre /\ _`, and the universal
`forall s, _ -> pre s` to `_ -> pre`. It carries all four observations, but
`obsDSP` and `obsASLP` **degenerate** — `obsDSP_is_obsASP` and
`obsASLP_is_obsDSLP` prove them pointwise equal to the angelic and
demonic-liberal readings, and `tripleDSP_is_tripleASP` /
`tripleASLP_is_tripleDSLP` carry that up to the triples. With no state there
is a single "input", so `R⁻¹(a) ⊆ pre` and `R⁻¹(a) ∩ pre ≠ ∅` say the same
thing whenever `R⁻¹(a)` is inhabited. See §3 for the carrier-level reason.

### Arrow-derived ASP/DSLP observations

The four `EffectObservations/SP/*_SPostArr.v` files observe computations into
the property-only stacks from `Arrows/SPostArr.v`. `Arrows/SPostArrMonad.v`
supplies named `Monad_Arrow` dictionaries for `ASPostArr S` and `DSLPostArr S`;
their laws follow from `MonadLawsE_Arrow`. Effects are stacked as arrows before
fixing the input to `unit`; `runASP` and `runDSLP` expose the familiar shape
`(S -> Prop) -> option (A * S) -> Prop`.

Each effect file defines `obsASP` directly from the computation's representation.
For example, the single-option nondeterministic observations use:

```coq
relASP (fun us r => unOptionT (runStateT m (snd us)) r)
```

`obsDSLP` is `asp_to_dslp` applied to `obsASP`. The conversion preserves the
recovered relation and the monad operations, so the DSLP return/bind proofs
reuse the ASP proofs. The nondeterministic files combine generic arrow
normalization with computation-owned raw laws; the double-option file derives
a local slice bind adapter and slice get/put/raise/`pickP` facts from those
laws. The ITree file uses convergence facts. Both observations preserve the
exact arrow-derived return and bind.

`SPostArrObservation.v` supplies `tripleASP` and `tripleDSL` over an observed
specification. Each effect file specializes those judgments to programs via
its `obsASP`/`obsDSLP`. The shared `*DefEq` theorems relate the `Over`/`Under`
judgments to comparisons against the raw `pp2_over`/`pp2_under` transformers;
apply them directly to an observed specification.

| Observation file | Source | Relation observed at `r : option (A * S)` | Meaning of `r = None` |
|---|---|---|---|
| `StDivITree_SPostArr.v` | `stdivitree` | `eutt eq (unOptionT (runStateT m s)) (Ret r)` | Terminating exception |
| `StExcNonDet_SPostArr.v` | `stexcnd` | `unOptionT (runStateT m s) r` | Exception |
| `StDivNonDet_SPostArr.v` | `stdivnd` | `unOptionT (runStateT m s) r` | Divergence |
| `StDivExcNonDet_SPostArr.v` | `stdivexcnd` | `unOptionT (unOptionT (runStateT m s)) (Some r)` | Terminating exception |

The last relation discards the outer divergence outcome; the `stdivnd`
observation keeps divergence visible, like `FullOutcomeObs`. Worked examples
check exception propagation, divergence visibility, nondeterministic writes,
and the ASP/DSLP distinction for many-to-one deterministic programs.

## 6. Comparing observations — `Taxonomy_*.v`

Three files assemble the inclusions, contrapositive pairs, and triple taxonomy,
one per source monad / target indexing. Observation modules also contain local
collapse and simplification results.

| File | Contents |
|---|---|
| `Taxonomy_StDivExcNonDet_StExc.v` | WP: inclusions (Thm 3.7), contrapositive transformers (Thm 3.8), `TaxonomyWPTransformers` (upper half of Figure 5). SP: `ContrapositiveTransformers`, `TaxonomySPTransformers`. Then `GaloisConnection`, joining the two, and `Module WithdrawExample`. |
| `Taxonomy_StDivNonDet_StExc.v` | `Module TaxonomyFullOutcome` — the contrapositive pairs, the `DSP_conjunction` / `ASLP_disjunction` decompositions, the four orderings, and the `cc_*` / `ii_*` triple taxonomy. |
| `Taxonomy_StDivNonDet_St.v` | `Module TaxonomyStDivNonDetWSt` (WP side) and `Module TaxonomyStDivNonDetSPSt` (SP side), each with its observation comparisons and triple taxonomy. |

`Section GaloisConnection` in the first file connects the WP and SP judgments.
The `dwlp_slice` and `awp_slice` lemmas express the WP readings through the
terminating relation used by SP. The resulting equivalences have specific
directions:

```text
dwlp_asp: tripleWP obsDWLP m pre SubsetOf post
          <-> tripleASP m Over pre post
awp_dslp: tripleWP obsAWP m pre SupersetOf post
          <-> tripleDSLP m Under pre post
```

These are not an identification of angelic WP coverage with ASP incorrectness;
the withdrawal example in §9 contrasts those judgments.

Where a taxonomy file holds both halves, the SP-side `Require Import`s are
placed *after* the WP sections rather than in the preamble, so the SP base-monad
modules cannot shadow names the WP proofs above resolve against.

## 7. The DM4all specification monads and their adjunctions

Five standalone base specification monads, faithful ports of the ones in
*Dijkstra Monads For All* (ICFP 2019), `theories/sprop/SpecificationMonads.v`.
Each is unary (`Type -> Type`) and has `Monad` and `MonadLawsE`. Their `Eq1`
compares underlying propositions by logical equivalence, so the law statements
do not require equality of bundled proofs. Assumptions should be checked for
the particular theorem, not inferred from a file's imports or this summary.

| file | module | carrier | DM4all name |
|---|---|---|---|
| `BaseSpecMonads/PredMonad.v` | `PredM` | `Pred A = A -> Prop` | `PredOM` |
| `BaseSpecMonads/PrePostMonad.v` | `PPM` | `PrePost A = Prop * (A -> Prop)` | `PPSpecMonad` |
| `BaseSpecMonads/SPostMonad.v` | `SPM` | `SPost A = { f : forall p, A -> Over p \| sp_mono f }` | `ForwardPredTransformer` |
| `BaseSpecMonads/WPureMonad.v` | — | `WPure A = { f : (A -> Prop) -> Prop \| wpure_mono f }` | `WPure` |
| `BaseSpecMonads/RelPrePostMonad.v` | `RPPM` | `RelPrePost X = { r : forall p, (X -> Assuming p) -> Assuming p \| rpp_mono r }` | `MRSpec` |

The carrier constraints explain two important proof steps. `Over p` stores a
proposition that implies `p`; the `SPost` associativity proof uses that implication
to recover an intermediate witness. `Assuming p` stores a proposition `q` with
`q <-> (p -> q)`; `ab_close` discharges the leading assumption in the
`RelPrePost` left-unit proof.

`BaseSpecMonads/BaseGaloisConnections.v` defines the orders (`Pred_le`,
`PP_le`, `SP_le`, `MR_le`, each with its `PreOrder` instance; `WP_le` comes from
`WPureMonad.v`) and establishes DM4all's `Section Adjunctions` results:

| theorem | statement |
|---|---|
| `pred_pp_adjunction` | `PP_le (pred2pp post) pp <-> Pred_le post (pp2pred pp)` |
| `wp_pp_under_adjunction` | `PP_le pp (wp2pp_under w) <-> WP_le (pp2wp_under pp) w` |
| `wp_mr_adjunction` | `WP_le w (mr2wp r) <-> MR_le (wp2mr w) r` |
| `sp_pp_adjunction` | `PP_le (sp2pp sp) pp <-> SP_le sp (pp2sp pp)` |
| `sp_mr_adjunction` | `MR_le (sp2mr sp) mr <-> SP_le sp (mr2sp mr)` |

plus the unit/counit round trips, each obtained by instantiating an adjunction
at reflexivity (`pp2sp_sp2pp_loop` / `sp2pp_pp2sp_loop` are DM4all's).

`WP_le` and `MR_le` are *reversed* — a weaker demand is lower.

`pp2sp` uses an impredicative intersection: `pp2spBase` quantifies over every
`SPost` above `fun p a => p /\ PPM.post pp a`. Its underlying proposition
depends only on `PPM.post pp`, not on the pair's precondition. The theorem
`pp2sp01` compares it with the simpler candidate
`pp2sp0 pp = fun p a => p /\ (PPM.pre pp -> PPM.post pp a)`.

This adjunction does not supply the ASP under-approximation target used in §3.
That target belongs to `NewGaloisConnections.v`, whose characterization uses
`ordASPStExcAt` at the asserted precondition. The DM4all unary carrier and the
stateful ASP carrier have different contracts.

The file does *not* `Import PPM`: `PPM` binds `pre` and `post`, which would
capture the binders of the SP embeddings, so `PPM.pre` / `PPM.post` are written
throughout.

### `NewGaloisConnections.v` — PrePost against the SP monads

Builds on `BaseGaloisConnections.v` with the second `PrePost -| WPure`
adjunction (`wp_pp_over_adjunction`, over the *over* pair
`wp2pp_over`/`pp2wp_over`) and then, in `Section SPPrePostEmbeddings`:

- `approxKind` (`Under` / `Over`)
- the four in-monad targets `pp2asp_over` / `pp2asp_under` / `pp2dslp_under` /
  `pp2dslp_over`, and the unrestricted pair `pp2_over` / `pp2_under`
  that the `triple*spec` forms compare against
- the `_at` collapse lemmas `tASPunder_at` / `tDSLPover_at`
- the four in-monad characterizations `gen_asp_over` / `gen_asp_under` /
  `gen_dslp_under` / `gen_dslp_over`

Two modules repeat the section at the other outcome types:

- `Module StSP` — the terminating slice, where the targets are
  `pp2asp_over` / `tASPunder` / `pp2dslp_under` / `tDSLPover` and land in
  `ASPSt` / `DSLPSt`.
- `Module PureSP` — the state-free case, where the Hoare pair is a
  `PPM.PrePost A` (so `pre : Prop`, `post : A -> Prop`) and the targets land in
  `ASPSP` / `DSLPSP`. The shapes collapse by dropping the witness:
  `exists s, p s /\ _` becomes `p /\ _`, and `forall s, _ -> p s` becomes
  `_ -> p`. Its two side conditions are the pure shadows of the stateful ones —
  `exists s, pre s` becomes `pre`, `exists s, ~ pre s` becomes `~ pre` — and
  are justified by `asp_bot_pure` / `dslp_top_pure` in the monad files.

The `gen_*` theorems apply to an **arbitrary** `w` in the relevant monad.
They can therefore characterize an observed specification without depending
on the computation that produced it. Observation files also expose local
versions of these triple characterizations.

### Relation to `Arrows/GaloisArr.v`

`Arrows/GaloisArr.v` proves four binary connections: `Galois_Rel_PrePost`,
`Galois_Rel_SPost`, `Galois_WP_PrePost`, and `Galois_RPP_WP`. Its local
`MonotoneSPost`, `MonotoneWP`, and `WFRelPrePost` subtypes state the required
constraints. `Galois_Rel_SPost` is an adjunction with monotone transformers,
not an isomorphism on that entire carrier; the property-only ASP normal form
in §8 requires the stronger strictness and disjunctivity conditions.

The file also proves `gamma_uni_not_monotone`, rejecting one proposed
SP/validator map. Its existential alternative remains informal discussion.
These results do not establish that every binary version of a unary adjunction
must fail.

When comparing presentations, keep the precondition shape explicit.
`(S -> Prop) -> X` accepts one predicate on all initial states; `S -> Prop -> X`
accepts a proposition at each state. These types are not related by currying,
and substituting one for the other changes the quantifiers in a triple.

## 8. Arrows vs monads: file split

Each specification family has separate **unary monad and binary arrow
presentations**:

| family | monad (unary carrier) | arrow (binary carrier) |
|---|---|---|
| `Pred` / `Rel` | `BaseSpecMonads/PredMonad.v` — `Pred A = A -> Prop` | `Arrows/Rel.v` — `Rel A B = A -> B -> Prop` |
| `PrePost` | `BaseSpecMonads/PrePostMonad.v` — `PrePost A = Prop * (A -> Prop)` | `Arrows/PrePostArr.v` |
| `SPost` | `BaseSpecMonads/SPostMonad.v` — `SPost A` over `Over p` | `Arrows/SPostArr.v` — property-only `PureASPostArr`, `PureDSLPostArr`; `Arrows/RelSPostArr.v` — ASP/DSLP readings of the existing `Rel` carrier |
| `RelPrePost` | `BaseSpecMonads/RelPrePostMonad.v` — over `Assuming p` | `Arrows/RelPrePostArr.v` |
| `WPure` / `WP` | `BaseSpecMonads/WPureMonad.v` | `Arrows/WPArr.v` |

The five unary specification-monad files define their carriers **in terms of the result type alone**
(`Pred A = A -> Prop`), rather than fixing the input of a binary arrow.
`WPArr.v` reuses the raw carrier `WPureT`.
`PredicateTransformerProperties.v` defines binary SP healthiness
properties independently of the base-monad development.

General arrow infrastructure lives in `Code/Classes/`. `ArrowMonad.v` defines
the generic return/bind operations for `arr I` and proves their monad laws;
`ArrowApplyFacts.v` supplies the shared algebraic application and arrow
extensionality lemmas used by the monad and option-transformer proofs.
`ArrowMorphism.v` packages maps that respect the selected source and destination
equalities, proves operation preservation, and lifts the maps through option/state.
`RelArrowCoherence.v` derives complete core, choice, and application law
packages from relational operation contracts and `RelArrowEq`, which connects
the chosen arrow equivalence to pointwise relation equivalence. Its
relational-only helpers do not require equality reflection.
The retained `rel_state_option_pure` and
`rel_state_option_bind` theorems also normalize the actual arrow-derived
return and bind of a state-over-option stack at any fixed input type `I`.
Bind keeps the input, threads the intermediate state, and propagates `None`.
The SP monads use `rel_state_option_bind_fields` with their operation facts;
`ASP_rel_presentation` and `DSLP_rel_presentation` also expose the bundled
exact-equality interface for independent consumers; the direct-Rel equivalences
below do not use it. Concrete proofs retain the assumptions used to establish
their relational readings.
Canonical SP carriers and their relational contracts live in
`BaseSpecMonads/*ArrowCore.v` / `*ArrowRel.v`; the compatibility interface,
representation morphisms, and loop obstruction live in `Taxonomy/Arrows/`.

### Arrow-derived monad laws

`ArrowLaws` includes `first_natural`: applying a pure function to the carried
component commutes with running the first arrow. `ArrowApplyLaws` includes the
fixed-arrow `app_law`, the standard pairing/precomposition/postcomposition
equations (`app_unit`, `app_precompose`, `app_postcompose`), and `app_ext`.
The last field makes application respect equivalent arrows stored in its input
values, which is needed when replacing a bind continuation pointwise.

For every input type `I`, `MonadLawsE_Arrow` derives left identity, right
identity, associativity, and `Proper_bind` from these law classes. Its target
names the exact operations and equality:

```coq
@MonadLawsE (arr I) (@Eq1_Arrow arr HE I)
  (@Monad_Arrow arr HA HAA I)
```

Here `HA`, `HAA`, and `HE` are the arrow, application, and equality dictionaries.
`Eq1_Arrow` restricts `arrow_eq` to `arr I`; it is an explicit definition so it
does not compete with concrete monads' `Eq1` instances. The global
`Eq1Equivalence_Arrow` and `MonadLawsE_Arrow` instances resolve for these explicit
dictionaries. The derivation needs no inhabitant of `I`; concrete instances
retain the assumptions of their own law proofs.

The concrete arrows register their chosen `Eq1` aliases. Generic instances
provide `Monad`, `Eq1Equivalence`, and `MonadLawsE`. Test-only named dictionary
aliases and compact return/bind agreement proofs live in `Arrows/Tests/`.
Production modules retain the compact Pred and RelPrePost operations used by
their mathematical consumers, and `SPostArrMonad.v` retains the two named
stack dictionaries used by effect observations.

The option and state arrow transformers preserve the full law contract, so
the same monad-law proof applies at each layer:

```text
lawful base arrow
       | optionArrT (also requires lawful ArrowChoice)
       v
lawful option arrow
       | stateArrT S
       v
lawful state-over-option arrow
       | fix input I; use MonadLawsE_Arrow
       v
lawful monad on stateArrT S (optionArrT arr) I
```

`Classes/Tests/ArrowMonadRegression.v` checks generic law resolution and a
counterexample: a lawful arrow whose application satisfies the old fixed-arrow
law but violates monad right identity. The stronger application contract
rejects it. `Arrows/Tests/ArrowMonadInstances.v` collects the concrete monad,
`Eq1Equivalence`, and `MonadLawsE` dictionaries of the specification arrows
together with their compact relational `ret`/`bind` descriptions and agreement
facts. It checks the exact derived monad dictionary for `Rel`, the property-only
ASP/DSLP carriers, and the other specification arrows, using their selected
equalities. Base, option, state, and state-over-option checks include non-unit
inputs. The relational checks serve both `asp` and `dslp` readings; the readings
do not need separate monad dictionaries. Named concrete dictionaries are also
checked against the generic dictionary, with automatic law resolution under
their canonical equalities.
`Arrows/Tests/ArrowTransformerInstances.v` holds the transformer-stack
resolution checks: the `optionRel` and relational state-over-option laws,
the monad-view `progRelM` / `nditRelM` stacks, and the double-option
application-law witnesses. Relational arrow-stack dictionaries resolve through
the generic transformers. The file also checks the definition of
property-only pointwise equality, automatic base core/choice/application law
resolution, and semantic `app_ext` and bind-continuation congruence for both
ASP and DSLP.
Both test modules are in `_CoqProject`, so the normal build checks them.
They register no helper instances. Explicit generic applications check
specialization; `:= _` checks automatic resolution. The two named SP-stack
law witnesses use explicit applications to pin the exact dictionaries and avoid
competing recursive option/state search paths. `CanonicalSP` additionally checks
cross-API application and bind, pure/state clients, runner identity, and a state
update followed by propagated failure.

### Relational SP readings

[`Arrows/RelSPostArr.v`](Arrows/RelSPostArr.v) computes two SP readings of the
existing `Rel A B := A -> B -> Prop` carrier. **An arrow value is a relation**,
not a pair of a relation and a transformer or a new wrapper:

```text
asp  R P b = exists a, P a /\ R a b
dslp R P b = forall a, R a b -> P a
```

ASP asks for some predecessor in the precondition; DSLP requires every
predecessor to satisfy it. At an unreachable output, ASP is false and DSLP is
vacuously true. This also holds when the input type is empty. Determinism alone
does not identify the readings: for the constant function `bool -> unit` and
precondition `eq true`, ASP holds at `tt`, but DSLP fails because `false` is
also a predecessor.

Both readings use `Arrow_Rel`, `ArrowChoice_Rel`, `ArrowApply_Rel`, and their
existing laws in [`Rel.v`](Arrows/Rel.v). The selected equality remains
`Rel_eq`, namely `forall a b, R a b <-> R' a b`. The same `optionRel` and
`progRelArr` stacks serve both readings; choosing `asp` or `dslp` changes the
predicate transformer, not the relation, its operations, or its law packages.

`RelSPostArr.v` also retains `asp_inv` / `dslp_inv` and their recovery facts.
The reverse transformer round trips concern transformers in the image of the
respective reading, not arbitrary raw transformers. `dsp_asp_dslp` and
`aslp_asp_dslp` characterize the DSP and ASLP readings as the conjunction and
disjunction of ASP and DSLP over the same relation.

These results follow Lena Verscht and Benjamin Lucien Kaminski,
[*A Taxonomy of Hoare-Like Logics: Towards a Holistic View using Predicate
Transformers and Kleene Algebras with Top and Tests*](https://doi.org/10.1145/3704896),
POPL 2025. Definitions 3.5 and 3.6 give the DSP and ASLP readings; §3.2.4 gives
the conjunction/disjunction identities.

### Property-only SP arrows

`Arrows/PredicateTransformerProperties.v` defines `StrictArr`,
`TerminatingArr`, `ConjunctiveArr`, and `DisjunctiveArr` for
`(A -> Prop) -> B -> Prop`, following Ralph-Johan Back and Joakim von Wright,
*Refinement Calculus: A Systematic Introduction* (1997 draft, §16.1; published
1998). The [terminology source note](Arrows/PROPERTY_TERMINOLOGY.md#sources-and-verification-limits)
identifies the version consulted. Conjunctivity and disjunctivity preserve
arbitrary **nonempty** families. Strictness supplies empty-join preservation;
termination supplies empty-meet preservation. Here, termination means **top
preservation**, with its operational interpretation determined by the direction
of the transformer.

The canonical ASP/DSLP carriers store only a transformer and healthiness proofs,
including explicit monotonicity. `Arrows/SPostArr.v` exposes compatibility aliases
to the public carriers in `BaseSpecMonads/`:

```coq
PureASPostArr A B := ASPArr A B.
PureDSLPostArr A B := DSLPArr A B.
```

The accessors are `getASP` and `getDSLP`. `arrASP` / `arrDSLP` lift functions;
`arrASP_spec` / `arrDSLP_spec` expose their direct and universal images.
Composition forwards the precondition:
`comp f g P = g (f P)`. Application satisfies these normal-form equivalences:

```text
appASP  P b <-> exists f, getASP  f (fun a => P (f,a)) b
appDSLP P b <-> forall f, getDSLP f (fun a => P (f,a)) b
```

The compatibility operations and dictionaries are definitions over the canonical
ones, with no duplicate global registrations. Both carriers satisfy `ArrowLaws`,
`ArrowChoiceLaws`, and `ArrowApplyLaws`.
The existing option/state transformers lift these laws, including to
`stateArrT S (optionArrT PureASPostArr)` and its DSLP counterpart. This stack
has input `A * S` and output `option (B * S)`: `None` propagates without a final
state. `ASPostArr S B` and `DSLPostArr S B` fix the arrow input to `unit`; they
are definitionally the public `ASPStExc S B` / `DSLPStExc S B` monads, including
their return/bind dictionaries.

Property-only `arrow_eq f g` means pointwise transformer iff:
`forall P b, getASP f P b <-> getASP g P b`, and likewise for DSLP.
`Proper_getASP` / `Proper_getDSLP` support rewriting through accessors.
Composition, first, choice, application, and arrow-derived bind respect this
equivalence, including pointwise-equivalent continuations.

`SPostArr.v` groups the recovered relations `ASP_rel` / `DSLP_rel` with
`relASP` / `relDSLP`, their round trips, and normal-form rewrite consequences.
Their operation-preservation facts use the existing operators in `Rel.v`.
All four canonical SP carriers instantiate the shared `RelArrow`,
`RelArrowChoice`, `RelArrowApply`, and `RelArrowEq` contracts in
`Classes/RelArrowCoherence.v`. Those contracts supply their complete
core/choice/application law packages under pointwise transformer iff.
The ASP/DSLP normal forms and base law packages are constructive; exact bundled
equality remains available separately with extensionality. DSP/ASLP recovery and
law packages retain classical reasoning. The relational carrier reuses its
existing laws in `Rel.v`.
The generic transformers preserve both sets of laws algebraically.

### Equivalence with `Rel`

[`SPostArrEquiv.v`](Arrows/SPostArrEquiv.v) relates each property-only carrier
directly to `Rel`, using the existing maps in `SPostArr.v`:

| Property-only carrier | Map to `Rel` | Map from `Rel` | Packaged morphisms (to / from) |
|---|---|---|---|
| `PureASPostArr` | `ASP_rel` | `relASP` | `asp_to_rel_morphism` / `asp_from_rel_morphism` |
| `PureDSLPostArr` | `DSLP_rel` | `relDSLP` | `dslp_to_rel_morphism` / `dslp_from_rel_morphism` |

The round-trip theorems are `asp_from_to` / `asp_to_from` and
`dslp_from_to` / `dslp_to_from`. They use the selected `arrow_eq` on the
property-only side and `Rel_eq` on the relational side. For example,
`asp_from_to` states `arrow_eq (relASP (ASP_rel f)) f`, while `asp_to_from`
states `Rel_eq (ASP_rel (relASP R)) R`.

Each conversion preserves its SP reading:
`asp (ASP_rel f) P b <-> getASP f P b`, and likewise for DSLP. In the other
direction, `getASP (relASP R)` computes `asp R`, while `getDSLP (relDSLP R)`
computes `dslp R`. This equivalence does not identify ASP with DSLP.

The existing `ArrowMorphism` record takes explicit source and destination
`ArrowEq` dictionaries. Its `morphism_proper` field requires the map to respect
those equalities. Its five operation fields preserve pure, composition, first,
choice (`left`), and application under the destination `arrow_eq`.
`morphism_app` converts the arrow stored in the application's input as well as
the application itself. `SPostArrEquiv.v` uses the module aliases
`PropertySP := SPostArr` and `RelSP := RelSPostArr`.

The public option and state-over-option maps reuse the generic lifts in
`Classes/ArrowMorphism.v`:

| Layer and reading | Map to the `Rel` stack | Map from the `Rel` stack |
|---|---|---|
| Option ASP | `option_asp_to_rel` | `option_asp_from_rel` |
| Option DSLP | `option_dslp_to_rel` | `option_dslp_from_rel` |
| State-over-option ASP | `state_option_asp_to_rel` | `state_option_asp_from_rel` |
| State-over-option DSLP | `state_option_dslp_to_rel` | `state_option_dslp_from_rel` |

Each map's morphism theorem appends `_morphism`. Lifted round-trip names keep
the same pattern, such as `option_asp_from_to` / `option_asp_to_from` and
`state_option_asp_from_to` / `state_option_asp_to_from`, with DSLP counterparts.
All public lifted round trips and operation-preservation results use the
corresponding selected `arrow_eq`. State-only lifts use `state_arrow_map` and
`state_arrow_morphism` directly.

Inverse and lift proofs use the existing core/choice/application laws under
the selected equality dictionaries. Inverse application uses `app_ext`; state
lifting uses the law-derived `pure_ext`. See the
[Classes contract](../Classes/CONTEXT.md#contracts)
for each generic theorem's law requirements. The direct-Rel equivalences do
not reflect `Rel_eq` into ordinary equality or use Leibniz law dictionaries.

`ArrowEq_leibniz` and the property-only `ArrowLaws_*_leibniz` /
`ArrowChoiceLaws_*_leibniz` helpers remain independent APIs, not prerequisites
for these equivalences. `PureASPostArr_eq` / `PureDSLPostArr_eq` also remain
available to recover equality of bundled property-only arrows where needed.
Consult the [assumption audit](../Checks/CONTEXT.md) for selected theorem
dependencies.

Checked clients live in `Arrows/Examples/SPostArrExamples.v`; monad and
transformer instantiation checks live in `Arrows/Tests/`.

`Arrows/OptionLoop.v` proves that `optionRel` cannot satisfy unrestricted
`ArrowLoop` left tightening: empty feedback makes failure propagation conflict
with the empty relation. `SPostArrEquiv.v` transports this obstruction through
the direct-Rel option maps to property-only ASP and DSLP.
`optionASP_no_left_tightening` / `optionDSLP_no_left_tightening` and their
`optionASP_no_lawful_ArrowLoop` / `optionDSLP_no_lawful_ArrowLoop` corollaries
use the selected pointwise equalities. They concern the existing option
operations with feedback ranging over all types, including `Empty_set`, not
every possible feedback design.

The local transport helper still needs one exact source-carrier substitution:
an arbitrary `ArrowLoop` has no congruence field for replacing a loop body by
an equivalent arrow. Existing property-only extensionality justifies equality
of those source arrows from equivalence of their recovered relations, allowing
substitution under the loop. The projection's round-trip and operation facts,
and the public obstruction statements, remain semantic. This local step does
not convert `Rel_eq` into equality of relation values.

`PredMonad.v` also carries `WPred` and the stack
`ProgWPred S := stateT S (optionT WPred)`. `WPred` and `PredM.Pred` use the
same predicate shape but have separate equality dictionaries: Leibniz equality
for `WPred` and pointwise logical equivalence for `PredM.Pred`. Check the
selected `Eq1` when using their laws.

## 9. Example programs

`ExampleProgramDefs.v` holds the program definitions and nothing else:

| program | monad | notes |
|---|---|---|
| `progA`, `progB`, `progRet`, `progEx` | `stdivexcnd` | `progB` has a divergent branch |
| `example_state` | `stdivexcnd (nat*nat*nat)` | O'Hearn, *Incorrectness Logic*, Example 3.1 |
| `progloom`, `progloom_harder` | `stdivexcnd` | the withdrawal session |
| `progA_stexcnd` | `stexcnd` | `progA` read in the divergence-free monad |
| `progA_stdivitree` | `stdivitree` | the deterministic variant |

plus the shared `preEq0` / `postEq0`. The file imports no observations, so
different observation modules can use these programs without a cycle.

Three programs share the shape of `progA` in three different monads, so the two
transposed ones carry a monad suffix; `ExampleProgramDefs.v` imports more than
one nondeterminism monad, so `progA_stexcnd` writes `StExcNonDet.orP`
explicitly.

**Observation examples live with the observation they exercise** — the WP
examples for `stdivexcnd` at the end of `WP/StDivExcNonDet_WStExc.v`, the
ASP/DSP ones at the end of `SP/StDivExcNonDet_SPStExc.v`, and so on. A triple
means something different for each observation, so there is no single file where
they all belong.

The [raw semantic regressions](ComputationMonads/CONTEXT.md#semantic-regressions)
live beside the computation laws. They check empty-prefix blocking, failure
tokens surviving empty continuations, and `pickP` at `Empty_set` blocking.
At the observation interface,
[StDivExcNonDet_SPostArr.v](EffectObservations/SP/StDivExcNonDet_SPostArr.v)
proves `raiseP_obs_retained` and `spinP_obs_invisible`: the terminating slice
retains the exception but omits divergence.

The cross-reading example is `Module WithdrawExample`, at the bottom of
`EffectObservations/Taxonomy_StDivExcNonDet_StExc.v`: it states `tripleWP obsAWP`
with `SubsetOf` and `tripleASP … Under` over the *same* program and postcondition,
contrasting angelic *coverage* (∀ input, ∃ output) with O'Hearn-style bug
*presence* (∀ asserted output, ∃ input). It is a comparison, so it sits with the
other comparisons.

`InCorrectnessPrinciples.v` states O'Hearn's rewriting rules over the
`tripleASP` triples of `SP/StDivExcNonDet_SPStExc.v`.

## 10. `OldSP/`

`OldSPObservations.v`, `OldIncorrectnessRewritingRules.v`, and
`OldExamplePrograms.v` remain in the build. They preserve an earlier
reading-based presentation, now superseded by `BaseSpecMonads/` and
`EffectObservations/SP/`. Its compiled results include:

- the **additive / multiplicative** SP monads — `AdditiveSP`,
  `MultiplicativeSP`, `SPPure`/`PureSPM`, `SPStExc`/`ProgSPM`, the product monad
  `ProgSPB`, with their `Monad` / `Eq1` / `MonadLawsE` instances
- the **reading-based** presentation — `obsSP`, `spASP` / `spDSLP` / `spDSP` /
  `spASLP`, `readSP` / `readSPM` / `readJoin` / `readMeet`, `ofSet` / `ofCoSet`
- the four **no-go theorems** `no_ProgSP_for_obsDSP`, `no_ProgSPM_for_obsDSP`,
  `no_ProgSP_for_obsASLP`, `no_ProgSPM_for_obsASLP`, with their supporting
  counterexamples `obsDSP_not_top`, `obsASLP_not_strict`, `obsDSP_not_join2`,
  `obsASLP_not_meet2`
- the `AsSPObs` typeclass, `tripleSP` / `tripleSPm` / `tripleSPspec`,
  and `tripleJoin` / `tripleMeet`

The no-go theorems reject representing the DSP/ASLP readings in those earlier
additive/multiplicative carriers. They do not reject the current DSP/ASLP
monads or every possible sequencing construction.

Within `OriginalTripleSP`, `AsSPObs` selects ASP or DSLP from the existing
property-only `SPostArr.ASPostArr` / `SPostArr.DSLPostArr` types, using `getASP` /
`getDSLP`. Its plain-`Rel` instance chooses `asp`; the relation type itself does
not select between the two readings. See the [OldSP context](OldSP/CONTEXT.md).

The built `obsRel_bind` proof in [OldSPObservations.v](OldSP/OldSPObservations.v)
uses `StDivExcNonDet.outcomes_bind` directly. Its WP observation imports still
serve comparisons; computation-owned raw laws do not remove that dependency.

`OldSPObservations.v` also preserves a large **commented-out experiment**.
`AspConjugation`, `ObsRelM`, `ProgSPObs`, `SPredObs`, `SPredT`, and `ordSP`
inside that block are not compiled or exported. Its displayed proofs and
examples are historical notes, not current theorem references. The compiled
earlier presentation has its own local names, including `SPStExc`; do not
assume they denote the carriers in §3 or follow all conventions in §12.

`OldSP/Observation.v` and `OldSP/NonDetObservation.v` are **not** in
`_CoqProject`. They are the older observation style, kept for reference; the
directory's only `Admitted` is in `Observation.v`.

## 11. Build status

[`_CoqProject`](../_CoqProject) lists the normal build's sources. The
[root README](../../README.md#build) gives the build commands, and the
[opam manifest](../coq-spec-monad.opam) gives dependency constraints. A source
file can belong to the build while containing aborted attempts or disabled
experiments; neither is an exported theorem.

Build success, admissions, and logical assumptions are separate checks. Some
proofs use classical logic or extensionality. Use `Print Assumptions` on the
theorem of interest rather than inferring its assumptions from imports.

Run `make check` from `Code/` for assumption reports. The separate
[Checks/Assumptions.v](../Checks/Assumptions.v) reports all 13 laws in the stateful
raw outcome-law interface, the four double-option WP return laws, selected
arrow-derived observation laws and examples, and ordered-bind counterexamples.
Its WP `Check` commands instantiate theorem types; the semantic regression
proofs described in §9 belong to the normal build. See the
[Checks context](../Checks/CONTEXT.md) for audit scope and execution details.

The maintained [Code/Makefile](../Makefile) provides this opt-in target;
the audit file is outside `_CoqProject`, so ordinary `make` does not run it.
Each explicit `make check` reruns the reports and returns an error if the
audit file fails to compile. The reports cover selected declarations, not
every theorem in this README, and do not compare assumptions against an allowlist.

Not in the build, deliberately:

- `deprecated/` — earlier iterations. Ignore when grepping for symbol
  references.
- `OldSP/Observation.v`, `OldSP/NonDetObservation.v` — see §10.

The maintained `Code/Makefile` regenerates the gitignored `Makefile.coq` from
`_CoqProject` on every invocation. Verify source removals with a clean build
in an isolated checkout: stale `.vo` files can otherwise satisfy imports of
removed sources. Do not clean a shared workspace while another process is
building it. Editor backups (`.v~`) are outside the build manifest.

## 12. Naming conventions

**Instances** are named after the type they are an instance for, with the number
of underscores marking the layer:

| | pattern | examples |
|---|---|---|
| base monad | `Class_Type` (one underscore) | `Monad_WPure`, `MonadLawsE_WPure`, `Monad_Pred` |
| transformer stack | `Class__Type` (two underscores) | `Monad__WStExc`, `MonadState__WSt`, `Monad__ASPStExc`, `Eq1__DSPStExc`, `MonadLawsE__ASLPStExc`, `Monad__stdivnd` |

The law instance is always `MonadLawsE` (matching the ITree class), never
`MonadLaws`. Slice variants inside `Module St*` reuse the identical names; the
module qualifies them (`StASP.MonadLawsE__ASPSt`).

**Type names distinguish outcome indexings** — `SPSt` for plain pairs,
`SPStExc` for option outcomes. The latter can represent an exception or divergence
depending on the observation (§5):

| | option outcome | terminating slice (in `Module St*`) |
|---|---|---|
| type | `ASPStExc` | `ASPSt` |
| projection | `getASPStExc` | `getASPSt` |
| unit / bind | `retASPStExc` / `bindASPStExc` | `retASPSt` / `bindASPSt` |
| order | `ordASPStExc`, `ordASPStExcAt` | `ordASPSt`, `ordASPStAt` |

and likewise for `DSLP`, `DSP`, `ASLP`. The raw order is `ordSPStExc` /
`ordSPSt`; the WP side matches, with `ordWStExc` / `ordWSt`.

The state-free variants follow the same rule with `SP` in place of `SPSt` —
`ASPSP` / `DSLPSP`, `getASP` / `getDSLP`, `ordASPSP` / `ordASPSPAt` and
`ordDSLPSP` / `ordDSLPSPAt` — and, being at top level rather than in a `Module
St*`, they need no qualification.

The `Module St*` wrappers are still needed: the healthiness conditions
(`StrictProg`, `TerminatingProg`, …) and the `NewGaloisConnections.v` embeddings
deliberately carry parallel names in both variants, so the module is what tells
them apart.

## 13. Known duplication

The option-outcome and terminating-slice developments repeat carrier and order
structure. DSP/ASLP already share local recovery and congruence proofs in their
specification modules. Sequencing still differs in the propagation of `None`.
Factoring the full specification developments over an outcome type and its
sequencing laws remains a possible refactor, separate from sharing raw
computation laws.
