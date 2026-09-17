# Taxonomy

This directory is the core of the project. It defines a family of computation
monads, several families of specification monads, and *observations* connecting
them.

The organising principle:

> **The specification side never mentions a computation monad.** It is
> parameterised only by the *outcome type*.

Everything in `BaseSpecMonads/` compiles against ExtLib/ITree and the logic
axioms alone — that is the check that the separation is real. Everything that
depends on a particular computation monad lives in an observation file under
`EffectObservations/`, and amounts to just three things: `outcomes_bind`,
`outcomes_ret`, and the observations themselves.

A second separation runs alongside it: **defining** an observation and
**comparing** observations live in different files. `EffectObservations/WP/` and
`EffectObservations/SP/` define; `EffectObservations/Taxonomy_*.v` compare.

---

## 1. Directory layout

```
Taxonomy/
  ComputationMonads/     TransformerLaws            -- generic optionT/stateT/readerT laws
                         StDivITree, StExcNonDet, StDivNonDet, StDivExcNonDet,
                         DivNonDet, RdDivNonDet
  BaseSpecMonads/        Healthiness                 -- the four conditions, shared
                         PredMonad, PrePostMonad, SPostMonad, WPureMonad,
                         RelPrePostMonad             -- the five DM4all monads
                         SPPredicateTransformers     -- SP carriers + healthiness
                         ASPMonad, DSLPMonad, DSPMonad, ASLPMonad
                         SPHealthyMonads, WPHealthyMonads
                         BaseGaloisConnections, NewGaloisConnections
  Arrows/                PredArr, PrePostArr, RelPrePostArr, SPostArr, WPArr,
                         GaloisArr                   -- binary carriers
  EffectObservations/
      WP/                StDivITree_WStExc, StExcNonDet_WStExc,
                         StDivExcNonDet_WStExc, StDivNonDet_WSt,
                         StDivNonDet_WPHealthy
      SP/                StDivExcNonDet_SPStExc, StDivNonDet_SPStExc,
                         StDivNonDet_SPSt, DivNonDet_SPPure,
                         RdDivNonDet_RdSPPure
      (root)             Taxonomy_StDivExcNonDet_StExc,
                         Taxonomy_StDivNonDet_StExc, Taxonomy_StDivNonDet_St
  OldSP/                 the earlier reading-based SP presentation
  deprecated/            older iterations, excluded from the build
  (root)                 ExampleProgramDefs, InCorrectnessPrinciples
```

Observation files are named `<computation monad>_<specification target>.v`, so
the file name states exactly which observation it defines. Logical paths follow
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
| `rddivnd R A` | `readerT R divnd A` | `ComputationMonads/RdDivNonDet.v` | environment, nondeterminism, **divergence** |

`stexcnd` and `stdivnd` share a carrier and differ only in the *reading* of the
distinguished outcome `None`: an exception in the first, divergence in the
second. Nothing in the type distinguishes them; what fixes the meaning is which
operations are offered. `StExcNonDet.v` supplies `MonadExc` (`raiseP`/`catchP`);
`StDivNonDet.v` deliberately supplies none, and offers `divergeD`, `mayDiverge`
and `orD` instead. `None` is absorbing under `bind` either way, which is exactly
the propagation rule divergence needs, so the monad structure is identical. The
file and type names now carry that distinction, which used to live only in
comments.

`StDivNonDet.v` also carries `stdivndNE`, the non-empty fragment, which the
`WSt` observations need for healthiness.

`divnd` is the state-free base of that stack — `stdivnd S A = stateT S divnd A`
by `eq_refl` — standing to `StDivNonDet.v` as `SPPure` does to `SPSt` /
`SPStExc` on the specification side. It carries the same operations minus
`get`/`put` (`divergeD`, `orD`, `mayDiverge`), the same non-empty fragment
`divndNE`, and additionally the pointwise `outcomes_bind` /
`diverge_absorbing` / `mayDiverge_bind`, which are axiom-free.

`rddivnd` puts a read-only environment on that base instead of a state. The two
have the same shape but differ in the outcome:

```coq
stdivnd R A  =  R -> option (A * R) -> Prop     (* state: the outcome carries R *)
rddivnd R A  =  R -> option  A      -> Prop     (* reader: it does not          *)
```

so `RdDivNonDet.v` offers `MonadReader` (`ask`, `local`) where `StDivNonDet.v`
offers `MonadState` (`get`, `put`), and `nonEmpty_localD` is the extra closure
lemma the non-empty fragment needs.

Only `stdivexcnd` can distinguish the two effects, via its second `optionT`.

`TransformerLaws.v` holds the `Eq1`-generic `optionT` / `stateT` / `readerT`
monad-law instances that every stack in the development chains through — the
computation monads, `WPureMonad.v`'s `WSt` / `WStExc`, `PredMonad.v`'s
`ProgWPred`, and the `*Rd` specification monads. Each section is parametric in
the base monad (`Monad` / `Eq1` / `Eq1Equivalence` / `MonadLawsE` taken as a
`Context`) and names no concrete monad, so `BaseSpecMonads/` can depend on it
without depending on any computation monad — which is what keeps the
organising principle at the top of this file literally true.

The `readerT` instances are simpler than the `stateT` ones: the environment is
threaded but never returned, so no pairing has to be destructed in the law
proofs.

## 3. The four healthiness conditions, and the refinement recipe

There are two base predicate transformers, differing in which slot the
predicate argument occupies:

```coq
SPPure A = Prop -> (A -> Prop)          (* the argument is the PRECONDITION  *)
WPureT A = (A -> Prop) -> Prop          (* the argument is the POSTCONDITION *)
```

In both cases the monads are cut out by the same four conditions, stated once
in `Healthiness.v` for the shape they share, `PT I := (I -> Prop) -> Prop`:

```coq
Strict      w := ~ w (fun _ => False)
Terminating w := w (fun _ => True)
Conjunctive w := forall K, inhabited K -> forall p, w (fun i => forall k, p k i) <-> forall k, w (p k)
Disjunctive w := forall K, inhabited K -> forall p, w (fun i => exists k, p k i) <-> exists k, w (p k)
```

and paired into `AngelicTotal` (strict ∧ disjunctive), `DemonicLiberal`
(terminating ∧ conjunctive), `DemonicTotal` (strict ∧ conjunctive) and
`AngelicLiberal` (terminating ∧ disjunctive). `Conjunctive_MonoPT` /
`Disjunctive_MonoPT` mean monotonicity never has to be carried separately.

`WPureT A` **is** `PT A` on the nose. `SPStExc S A` is a *family* of `PT S`,
one per outcome, and `SPPredicateTransformers.v` proves the bridges —
`StrictProg_pointwise`, `ASP_pairing`, … — so the `*Prog` conditions are
literally the shared ones lifted pointwise, not merely analogous.

### How far the recipe carries: WP yes, SP no

| | WP (`WPHealthyMonads.v`) | SP (`SPHealthyMonads.v`) |
|---|---|---|
| distinct monads from four conditions | **four** | **two** |
| `ret`/`bind` shared across them | yes, `WPure`'s | no, genuinely different |
| the functor yields `MonadLawsE` | yes | no — per instance |
| lifts through `stateT`/`optionT` | yes, free | no |

**WP.** The four classes are pairwise incomparable on `PT A` — `wDem` is
conjunctive but not disjunctive, `wAng` the converse, `wTop` terminating but
not strict, `wBot` the converse (`Section Separation`). All four monads come
from one functor `HealthyWP` applied to the four conditions, *including*
`MonadLawsE`, because `bind` there is continuation composition and the closure
lemmas `Strict_bindPT` … `Disjunctive_bindPT` cover every case. And they stack:
`stateT` indexes by the initial state, `optionT` widens the outcome, neither
touches the postcondition slot the condition constrains, so

```coq
AWStExc S A = S -> AWPure (option (A * S))
```

is healthy by construction with its laws one line from `TransformerLaws.v`
(`Section Stacks`, all eight).

**SP.** Two separate failures:

1. *Only two monads.* `SPPure`'s precondition slot is a bare `Prop`, of which
   there are two up to propositional extensionality, so `Strict` alone forces
   `Singleton` and `Terminating` alone forces `MSingleton`. Hence
   `DemonicTotal ⟺ AngelicTotal` and `AngelicLiberal ⟺ DemonicLiberal`
   (`strict_conj_iff_singleton`, `term_disj_iff_msingleton`).

2. *No shared `ret`/`bind`.* The angelic and demonic monads have genuinely
   different operations, and the raw transformer type carries no monad
   structure for them to restrict:

   ```coq
   retASP  v = fun p a => p /\ a = v      bindASP  m k = fun p b => exists a, k a (m p a) b
   retDSLP v = fun p a => a = v -> p      bindDSLP m k = fun p b => forall a, k a (m p a) b
   ```

   So `HealthySP` takes `ret`/`bind` as parameters and shares only the
   packaging — carrier, projections, `Monad`, `Eq1`, `Eq1Equivalence`, orders —
   stopping short of the laws. `ASP_carrier_agrees` / `DSLP_carrier_agrees`
   (both `eq_refl`) and the four `*_agrees` lemmas show the recipe reproduces
   the hand-built `ASPSP` / `DSLPSP` exactly, so `ASPMonad.v` and `DSLPMonad.v`
   remain the definitions in use and `MonadLawsE` transports rather than being
   reproved.

And the stateful SP carriers are not transformer images of `SPPure` at all:
they take one **shared** `S -> Prop` precondition where any transformer over
`SPPure` gives a `Prop` **per** state, and `(S -> Prop) -> X` does not curry to
`S -> Prop -> X`. The canonical shared→pointwise map is not injective
(`fun pre _ => forall s, pre s` and the empty transformer have the same image).
That is why `DSPMonad.v` and `ASLPMonad.v` exist at their present size.

All of it traces to variance: the postcondition slot is where the continuation
composes, so preservation properties compose for free; the precondition slot is
upstream of the composition, and it is exactly where the SP distinctions live.

## 4. The SP specification monads

Predicate transformers `(S -> Prop) -> Outcome -> Prop`, carved into four
monads by four healthiness conditions. **The bare transformer type is not a
monad**; only these subsets are.

| Monad | Carrier condition | Equivalent healthiness class | Reading of a relation `R` |
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

**Why DSP and ASLP need machinery the other two don't.** Reading a relation as
an ASP is monotone in the relation and as a DSLP antitone, so those two orders
*are* relation inclusion. DSP and ASLP are neither monotone nor antitone
(`dspOf_not_monotone` / `dspOf_not_antitone` and duals), so their `bind` cannot
be a forward pass over the precondition. It instead **recovers** each argument's
relation by probing at two constant preconditions, composes the relations, and
re-reads — see `dsp_recov` / `aslp_recov` and the `*_carrier` bridges. Both
carriers are stated as healthiness conditions; `dsp_carrier` / `aslp_carrier`
prove these equivalent to the fixed-point form the proofs use.

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

Each module imports its predecessors (`StDSP` opens `StTrans StASP StDSLP`, and
so on), mirroring the top-level dependency chain. Separate per-file modules are
used rather than reassembling one combined module with `Include`, because
`Include` copies constants — the copies are convertible but display and unify
against the originals, which is a latent source of confusion.

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

`Strict` alone already forces `Singleton` (`strict_to_singleton`, using only
propositional extensionality and `NNPP` — `join_to_singleton` never used its
`Disjunctive` half), and `Singleton` returns *both* connectives
(`singleton_to_join`, `singleton_to_conjunctive`); dually for the multiplicative
side. So `DSPSP` and `ASPSP` are two presentations of the same subset of
`SPPure`, and their monad structure is **transported** along that equivalence
(`asp_to_dsp` / `dsp_to_asp`, both the identity on the underlying transformer)
rather than rebuilt — none of the relation-recovery machinery is needed.

What disappears is exactly what makes DSP interesting: a precondition that is a
*set* of states, so that `R⁻¹(r) ⊆ pre` carries more information than
`R⁻¹(r) ∩ pre ≠ ∅`. With one `Prop` in the precondition slot the two coincide.

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

Two consequences worth keeping straight. First, `ASPRd` coincides with what you
would get by defining a coupled carrier `(R -> Prop) -> A -> Prop` and cutting
it down by the ASP condition (strict + disjunctive): both are the relation
`R -> A -> Prop`, and their binds agree. Second, that coincidence **fails** for
DSP and ASLP: `DSPRd` inherits the pure collapse (`DSPSP = ASPSP`, above),
whereas strict + conjunctive on the coupled carrier does not collapse — the
transformer `fun pre _ => forall r, pre r` is strict and conjunctive but not
singleton, and it has no counterpart in `readerT R ASPSP`. So the pointwise
lift keeps ASP and DSLP faithfully but erases the DSP/ASLP distinction; only a
shared `R -> Prop` precondition retains it.

### In-monad characterizations

Only two of the eight triple directions are relation inclusions, and only those
work with the global order and no side condition:

| | `Over` | `Under` |
|---|---|---|
| ASP | `ordASPStExc obs (pp2asp_over …)` — global | `ordASPStExcAt pre (pp2asp_under …) obs` — needs `∃s, pre s` |
| DSLP | `ordDSLPStExcAt pre obs (pp2dslp_over …)` — needs `∃s, ¬pre s` | `ordDSLPStExc (pp2dslp_under …) obs` — global |
| DSP / ASLP | none | none |

`Over` always compares `obs ⊑ target`, `Under` always `target ⊑ obs`. The two
side conditions are forced by the healthiness conditions themselves (`asp_bot`:
every ASP is `False` at `⊥`; `dslp_top`: every DSLP is `True` at `⊤`) and are
not removable. DSP and ASLP have no in-monad target in either direction, because
their orders are not relation inclusion at all.

## 5. The WP specification monads

`BaseSpecMonads/WPureMonad.v` holds exactly three developments plus their
orders:

```coq
WPureT A   := (A -> Prop) -> Prop                    (* raw; used by Arrows/WPArr.v *)
wpure_mono f := forall p q, (p ⊆ q) -> f p -> f q
WPure  A   := { f : WPureT A | wpure_mono f }        (* the monad *)

WSt    S   := stateT S WPure                          (* W^St     *)
WStExc S   := stateT S (optionT WPure)                (* W^StExc  *)
```

`WSt S A = S -> (A * S -> Prop) -> Prop`: every outcome is a normal return, so
there is no `MonadExc`. `WStExc S A = S -> (option (A * S) -> Prop) -> Prop`:
the extra outcome is the raised exception, and it carries `MonadExc`.

`ret`, `bind`, `Eq1` (pointwise iff) and `MonadLawsE` are proved directly for
`WPure`; both stacks get their laws from the `Eq1`-generic `optionT` / `stateT`
instances in `ComputationMonads/StDivITree.v`.
`Coercion runWPure : WPure >-> Funclass` keeps application (`w post`) working
through the subset type.

Monotonicity is not decoration: `monotonicity_is_needed` shows the
`PrePost -| WPure` adjunctions are **false** without it. Because the carrier is
a subset type, each effect observation carries a monotonicity lemma
(`obsAWP_mono` and friends), and downstream proofs apply those rather than
`destruct`ing through the transformer.

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

### The four healthy WP monads

`WPHealthyMonads.v` cuts `WPure` into `AWPure` / `DWLPure` / `DWPure` /
`AWLPure` by the four pairings of §3, all from one functor `HealthyWP` —
`ret`, `bind`, `Monad`, `Eq1`, `Eq1Equivalence`, `MonadLawsE`, `ordW` and
`ordWAt` written once. `Section Separation` shows the four classes are pairwise
incomparable, and `Section Stacks` adds the eight `stateT` / `optionT` stacks
with inherited laws. See §3 for why this works here and not on the SP side.

**`Arrows/WPArr.v` deliberately stays on `WPureT`**, the unrestricted type: its
`ArrowEq` is Leibniz equality on functions into the carrier, which a subset type
cannot support without proof irrelevance, and its arrow laws hold definitionally
only for the raw type.

## 6. Observations

An observation maps a computation monad into the spec monads. Everything
downstream — monad-morphism theorems, triples, the taxonomy — follows from
`outcomes_bind` and `outcomes_ret`, whose case count tracks the effect layers.

Each file defines its observations, proves each is a **monad morphism**
(`obs*_ret` / `obs*_bind`), gives the `getProg*_obs*` readings, and builds the
triples over them together with their refinement (`*spec`) forms and `*DefEq`
equivalences. Comparisons between observations are *not* here — see §6.

### WP side — `EffectObservations/WP/`

| File | Source | Target | Observations | Module |
|---|---|---|---|---|
| `StDivITree_WStExc.v` | `stdivitree` | `WStExc` | all four | — |
| `StExcNonDet_WStExc.v` | `stexcnd` | `WStExc` | `obsDWP`, `obsAWP` only | — |
| `StDivExcNonDet_WStExc.v` | `stdivexcnd` | `WStExc` | all four | — |
| `StDivNonDet_WSt.v` | `stdivndNE` | `WSt` | all four | `TermSliceObsWP` |
| `StDivNonDet_WPHealthy.v` | `stdivndNE` | `stateT S {AWP,DWLP,DWP,AWLP}.W` | one per monad | `HealthyObsWP` |

The four readings are `obsDWP` (demonic total), `obsDWLP` (demonic liberal),
`obsAWP` (angelic total), `obsAWLP` (angelic liberal). `StExcNonDet_WStExc.v`
has no liberal readings because its monad has no divergence — they are not even
definable there. `StDivITree_WStExc.v` is the deterministic case and is the only
built file with `obsWPCollapse` / `obsWLPCollapse`, the angelic–demonic
collapse.

`StDivNonDet_WPHealthy.v` defines four effect observations, one into each
healthy monad of §5: `obsAWP` into `stateT S AWP.W`, `obsDWLP` into
`stateT S DWLP.W`, `obsDWP` into `stateT S DWP.W`, `obsAWLP` into
`stateT S AWLP.W`. Each target's healthiness condition is an obligation of the
definition, each observation is a monad morphism (`obs*_ret` / `obs*_bind`), and
`obs*_run` shows it has the same transformer as the corresponding `WSt`
observation below. Non-emptiness of the source is used only for `Strict` of
`obsDWP` and `Terminating` of `obsAWLP`.

`StDivNonDet_WSt.v` targets `WSt`, whose postconditions range over `A * S`, so
divergence is visible to the *observation* but not to the *postcondition*: the
total/liberal axis is carried entirely by which observation you pick. Its source
is the non-empty fragment `stdivndNE`, which is what makes the observations
healthy.

### SP side — `EffectObservations/SP/`

| File | Source | Target | Divergence visible in specs? | Module |
|---|---|---|---|---|
| `StDivExcNonDet_SPStExc.v` | `stdivexcnd` | `SPStExc` | **no** — reads the terminating slice | — |
| `StDivNonDet_SPStExc.v` | `stdivnd` | `SPStExc` | **yes** — `None` is an ordinary outcome | `FullOutcomeObs` |
| `StDivNonDet_SPSt.v` | `stdivnd` | `SPSt` | **no** — reads the terminating slice | `TermSliceObs` |
| `DivNonDet_SPPure.v` | `divnd` | `SPPure` | **no** — reads the terminating slice | `PureObs` |
| `RdDivNonDet_RdSPPure.v` | `rddivnd` | `ASPRd` / `DSLPRd` / `DSPRd` / `ASLPRd` | **no** — reads the terminating slice | `RdPureObs` |

Note the deliberate contrast in the fourth column:

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
  `Over` triple vacuously.

The two modules exist because `StDivNonDet_SPStExc.v` and `StDivNonDet_SPSt.v`
observe the same computation monad into differently-indexed targets, so their
`obsASP` and friends would otherwise clash.

`StDivNonDet_SPStExc.v` imports only its computation monad and the SP monads —
no sibling observation file. That is the intended shape for a new observation.

`RdDivNonDet_RdSPPure.v` threads the reader through the observation rather than
absorbing it: the target is the *same* transformer applied to the specification
side, `readerT R divnd A --> ASPRd R A = readerT R ASPSP A`, so each of its
laws is the corresponding `PureObs` law read at one environment. The four
targets `ASPRd` / `DSLPRd` / `DSPRd` / `ASLPRd` are defined in the SP monad
files themselves (§3). Its triples take `pre : R -> Prop` and are read
pointwise in the environment.

There is a genuinely different reading it does **not** cover: letting the
precondition range over *sets* of environments, `(R -> Prop) -> A -> Prop`.
That couples the environments the way a shared `S -> Prop` couples initial
states (§7), and is not any existing carrier, so it would need a new one.

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

## 7. Comparing observations — `Taxonomy_*.v`

Three files, one per source monad / target indexing, holding everything that
compares observations against one another rather than defining them: the
inclusions, the contrapositive pairs, and the resulting taxonomy of triples.

| File | Contents |
|---|---|
| `Taxonomy_StDivExcNonDet_StExc.v` | WP: inclusions (Thm 3.7), contrapositive transformers (Thm 3.8), `TaxonomyWPTransformers` (upper half of Figure 5). SP: `ContrapositiveTransformers`, `TaxonomySPTransformers`. Then `GaloisConnection`, joining the two, and `Module WithdrawExample`. |
| `Taxonomy_StDivNonDet_StExc.v` | `Module TaxonomyFullOutcome` — the contrapositive pairs, the `DSP_conjunction` / `ASLP_disjunction` decompositions, the four orderings, and the `cc_*` / `ii_*` triple taxonomy. |
| `Taxonomy_StDivNonDet_St.v` | `Module TaxonomyStDivNonDetWSt` (WP side) and `Module TaxonomyStDivNonDetSPSt` (SP side), each with its observation comparisons and triple taxonomy. |

`Section GaloisConnection` in the first file is the crossover: `dwlp_slice` and
`awp_slice` show that `obsDWLP` and `obsAWP` applied to a postcondition are the
two readings of the same terminating slice that `obsASP` / `obsDSLP` use, so
`dwlp_asp` and `awp_dslp` identify a WP triple with an SP triple — the triples
differ only in the order of the `s` and `r` quantifiers.

Where a taxonomy file holds both halves, the SP-side `Require Import`s are
placed *after* the WP sections rather than in the preamble, so the SP base-monad
modules cannot shadow names the WP proofs above resolve against.

## 8. The DM4all specification monads and their adjunctions

Five standalone base specification monads, faithful ports of the ones in
*Dijkstra Monads For All* (ICFP 2019), `theories/sprop/SpecificationMonads.v`.
Each is unary (`Type -> Type`), each has `Monad` + `MonadLawsE`, and every proof
is **axiom-free** — DM4all needs `Ssig_eq`, `sprop_ext` and funext for the same
results, which we avoid by taking `Eq1` to be pointwise iff rather than equality.

| file | module | carrier | DM4all name |
|---|---|---|---|
| `BaseSpecMonads/PredMonad.v` | `PredM` | `Pred A = A -> Prop` | `PredOM` |
| `BaseSpecMonads/PrePostMonad.v` | `PPM` | `PrePost A = Prop * (A -> Prop)` | `PPSpecMonad` |
| `BaseSpecMonads/SPostMonad.v` | `SPM` | `SPost A = { f : forall p, A -> Over p \| sp_mono f }` | `ForwardPredTransformer` |
| `BaseSpecMonads/WPureMonad.v` | — | `WPure A = { f : (A -> Prop) -> Prop \| wpure_mono f }` | `WPure` |
| `BaseSpecMonads/RelPrePostMonad.v` | `RPPM` | `RelPrePost X = { r : forall p, (X -> Assuming p) -> Assuming p \| rpp_mono r }` | `MRSpec` |

Two subtypes carry the weight. `Over p` (props that *imply* `p`) is what makes
`SPost`'s `bind_bind` typecheck; `Assuming p` (props closed under *assuming*
`p`, i.e. `q <-> (p -> q)`) is its dual and is exactly what `RelPrePost`'s
`bind_ret_l` needs — `ab_close` discharges the leading `p ->`.

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

Four of the five right/left adjoints are formulas. `pp2sp` is not: the obvious
candidate `pp2sp0 pp = fun p a => p /\ (pre pp -> post pp a)` is only a lax
inverse, so the real right adjoint is the impredicative **intersection** of every
`SPost` dominating the pair (`pp2spBase`), available because `Prop` is
impredicative. `pp2sp01` places it below `pp2sp0`.

Note that `pp2sp` mentions only `PPM.post pp`, never `PPM.pre pp`. The
intersection collapses to `post` itself, so `SP_le sp (pp2sp pp)` says exactly
`app sp True ⊆ post` — the *over*-approximate direction, independent of the
precondition. The under-approximate reading `post ⊆ app sp pre` is not an
instance of the global order at all; it is the order **scoped to one
precondition**, which is why the SP triples use `ordASPStExcAt` rather than
`ordASPStExc` in that direction.

The file does *not* `Import PPM`: `PPM` binds `pre` and `post`, which would
capture the binders of the SP embeddings, so `PPM.pre` / `PPM.post` are written
throughout.

### `NewGaloisConnections.v` — PrePost against the SP monads

Builds on `BaseGaloisConnections.v` with the second `PrePost -| WPure`
adjunction (`wp_pp_over_adjunction`, over the *over* pair
`wp2pp_over`/`pp2wp_over`) and then, in `Section SPPrePostEmbeddings`:

- `approxKind` (`Under` / `Over`)
- the four in-monad targets `pp2asp_over` / `pp2asp_under` / `pp2dslp_under` /
  `pp2dslp_over`, and the plain (non-healthy) pair `pp2_over` / `pp2_under`
  that the `triple*spec` forms compare against
- the `_at` collapse lemmas `tASPunder_at` / `tDSLPover_at`
- the four in-monad characterizations `gen_asp_over` / `gen_asp_under` /
  `gen_dslp_under` / `gen_dslp_over`

Two modules repeat the section at the other outcome types:

- `Module StSP` — the terminating slice, where the targets keep the
  `tASPover` / `tASPunder` / `tDSLPunder` / `tDSLPover` naming and land in
  `ASPSt` / `DSLPSt`.
- `Module PureSP` — the state-free case, where the Hoare pair is a
  `PPM.PrePost A` (so `pre : Prop`, `post : A -> Prop`) and the targets land in
  `ASPSP` / `DSLPSP`. The shapes collapse by dropping the witness:
  `exists s, p s /\ _` becomes `p /\ _`, and `forall s, _ -> p s` becomes
  `_ -> p`. Its two side conditions are the pure shadows of the stateful ones —
  `exists s, pre s` becomes `pre`, `exists s, ~ pre s` becomes `~ pre` — and
  are justified by `asp_bot_pure` / `dslp_top_pure` in the monad files.

The `gen_*` theorems are stated for an **arbitrary** `w` in the relevant monad;
each observation file obtains its own version by `exact`, since e.g.
`tripleASP m Over pre post` is *definitionally* the left-hand side.

### Relation to `Arrows/GaloisArr.v`

`GaloisArr.v` ports the same DM4all connections to this development's **binary
arrows** (`Pred A B`, `PrePost A B`, `WPArr A B`, `RelPrePost A B`), where two
of the five break: SP↔MR fails outright, and SP↔PP holds only with the
transformer restricted to the image of `asp` (`SingletonSPost`). Passing to the
unary monads removes both obstructions — the binary failures are artifacts of
the extra input index, not of the specifications.

The obstruction is in the precondition slot, not the state. `SPStExc S A =
(S -> Prop) -> option (A * S) -> Prop` has one `S -> Prop` *shared* across
states, and `(S -> Prop) -> X` does not curry to `S -> Prop -> X`. A shared
`S -> Prop` couples the initial states and makes the order strictly coarser than
pointwise.

## 9. Arrows vs monads: file split

Each specification family has **two independent presentations**, in separate
files, with no import edge in either direction:

| family | monad (unary carrier) | arrow (binary carrier) |
|---|---|---|
| `Pred` | `BaseSpecMonads/PredMonad.v` — `Pred A = A -> Prop` | `Arrows/PredArr.v` — `Pred A B = A -> B -> Prop` |
| `PrePost` | `BaseSpecMonads/PrePostMonad.v` — `PrePost A = Prop * (A -> Prop)` | `Arrows/PrePostArr.v` |
| `SPost` | `BaseSpecMonads/SPostMonad.v` — `SPost A` over `Over p` | `Arrows/SPostArr.v` — `PureASPostArr`, `PureDSLPostArr` |
| `RelPrePost` | `BaseSpecMonads/RelPrePostMonad.v` — over `Assuming p` | `Arrows/RelPrePostArr.v` |
| `WPure` / `WP` | `BaseSpecMonads/WPureMonad.v` | `Arrows/WPArr.v` |

The monad files define their carriers **in terms of the result type alone**
(`Pred A = A -> Prop`), never as a binary arrow with the input fixed. None of
them imports an arrow file; none of the arrow files imports a monad file.

The `*Arr.v` files still carry the *arrow's own* monad view — `Monad (Pred A)`
for a fixed input `A`, and in `SPostArr.v` the generic `ArrowApply -> Monad`
construction (`Section ArrowMonad`). Those live on the binary carrier, so they
stay with the arrow rather than in a monad file.
`OldSP/OldSPObservations.v` depends on the `Pred` one.

`PredMonad.v` also carries `WPred` and the stack
`ProgWPred S := stateT S (optionT WPred)`. `WPred` stays a definition in its own
right rather than an alias for `PredM.Pred`, even though the carriers are equal
and `bind` is identical: making it an alias would put two `Eq1` instances on one
type constructor (pointwise iff for `PredM`, Leibniz `eq` for the stack), and
each is load-bearing for its own laws.

**`PrePost` is strictly bigger than every SP monad.** `snd` composed with any SP
reading is a monad morphism, but it forgets the precondition and no injective
map exists (proved for the pure case). What does hold is a Galois connection
with each SP monad; for ASP it is order-preserving and for DSLP order-reversing.

## 10. Example programs

`ExampleProgramDefs.v` holds the program definitions and nothing else:

| program | monad | notes |
|---|---|---|
| `progA`, `progB`, `progRet`, `progEx` | `stdivexcnd` | `progB` has a divergent branch |
| `example_state` | `stdivexcnd (nat*nat*nat)` | O'Hearn, *Incorrectness Logic*, Example 3.1 |
| `progloom`, `progloom_harder` | `stdivexcnd` | the withdrawal session |
| `progA_stexcnd` | `stexcnd` | `progA` read in the divergence-free monad |
| `progA_stdivitree` | `stdivitree` | the deterministic variant |

plus the shared `preEq0` / `postEq0`. It is a leaf so that observation files and
example blocks can both use the programs without a cycle.

Three programs share the shape of `progA` in three different monads, so the two
transposed ones carry a monad suffix; `ExampleProgramDefs.v` imports more than
one nondeterminism monad, so `progA_stexcnd` writes `StExcNonDet.orP`
explicitly.

**The worked examples live with the observation they exercise** — the WP
examples for `stdivexcnd` at the end of `WP/StDivExcNonDet_WStExc.v`, the
ASP/DSP ones at the end of `SP/StDivExcNonDet_SPStExc.v`, and so on. A triple
means something different for each observation, so there is no single file where
they all belong.

The one exception is `Module WithdrawExample`, at the bottom of
`Taxonomy_StDivExcNonDet_StExc.v`: it states `tripleWP obsAWP` and
`tripleASP … Under` over the *same* program with the *same* postcondition,
contrasting angelic *coverage* (∀ input, ∃ output) with O'Hearn-style bug
*presence* (∀ asserted output, ∃ input). It is a comparison, so it sits with the
other comparisons.

`InCorrectnessPrinciples.v` states O'Hearn's rewriting rules over the
`tripleASP` triples of `SP/StDivExcNonDet_SPStExc.v`.

## 11. `OldSP/`

`OldSPObservations.v` (2844 lines) and `OldIncorrectnessRewritingRules.v` hold
the earlier reading-based presentation of the SP side, superseded by
`BaseSpecMonads/` + `EffectObservations/SP/` but **not** redundant. It is the
only place with:

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
  `tripleJoin` / `tripleMeet`, and the `ProgSPObs` / `SPredObs` modules

The no-go theorems matter beyond history: they are the machine-checked reason
`DSPStExc` / `ASLPStExc` are built by *recovering* relations rather than by a
forward pass, and nothing in the current files records that argument.

`OldSP/` keeps its own vocabulary (`SPredT`, `ordSP`) and is not part of the
naming scheme in §12.

`OldSP/Observation.v` and `OldSP/NonDetObservation.v` are **not** in
`_CoqProject`. They are the older observation style, kept for reference; the
directory's only `Admitted` is in `Observation.v`.

## 12. Build status

`_CoqProject` lists 75 files and builds **clean from scratch**, with **no
`Admitted`**. The five DM4all base monads and their adjunctions are axiom-free;
classical reasoning enters on the multiplicative/demonic side
(`Classical_Prop`), and several files also import `PropExtensionality` /
`FunctionalExtensionality`. Run `Print Assumptions` on a specific result if you
need its exact footprint.

Not in the build, deliberately:

- `deprecated/` — earlier iterations. Ignore when grepping for symbol
  references.
- `OldSP/Observation.v`, `OldSP/NonDetObservation.v` — see §10.

`Makefile` is gitignored; regenerate with
`coq_makefile -f _CoqProject -o Makefile`. A stale `.vo` still satisfies a
`Require`, which has masked a broken build during past reorganisations — if
`_CoqProject` changes, rebuild from clean. There are a few `.v~` editor backups
under `OldSP/` and `BaseSpecMonads/`; the build ignores them.

## 13. Naming conventions

**Instances** are named after the type they are an instance for, with the number
of underscores marking the layer:

| | pattern | examples |
|---|---|---|
| base monad | `Class_Type` (one underscore) | `Monad_WPure`, `MonadLawsE_WPure`, `Monad_Pred` |
| transformer stack | `Class__Type` (two underscores) | `Monad__WStExc`, `MonadState__WSt`, `Monad__ASPStExc`, `Eq1__DSPStExc`, `MonadLawsE__ASLPStExc`, `Monad__stdivnd` |

The law instance is always `MonadLawsE` (matching the ITree class), never
`MonadLaws`. Slice variants inside `Module St*` reuse the identical names; the
module qualifies them (`StASP.MonadLawsE__ASPSt`).

**Type names match their carriers** — `SPSt` for the terminating slice,
`SPStExc` for the exception outcome:

| | exception outcome | terminating slice (in `Module St*`) |
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

## 14. Known duplication

The option-outcome and terminating-slice developments are near-copies differing
only in the outcome type, `bind`, and the four `comp_*` lemmas — everything else
transfers by re-indexing. Parameterising one development over an abstract
outcome functor plus a Kleisli `step` (with the three `comp_*` laws as
hypotheses) would share the bridges, carriers and targets, and reduce each new
outcome type to one instance. `ASLPMonad.v` is the worst case at 1303 lines.
