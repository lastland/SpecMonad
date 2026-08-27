# Taxonomy

This directory is the core of the project. It defines a family of computation
monads, a family of strongest-postcondition (SP) specification monads, and
*observations* connecting them.

The directory has been through one substantial refactor. The organising
principle of the current design is:

> **The specification side never mentions a computation monad.** It is
> parameterised only by the *outcome type*.

`SPSpecMonads.v` compiles standalone against ExtLib/ITree and the logic
axioms — that is the check that the separation is real. Everything that depends
on a particular computation monad lives in an observation file, and amounts to
just three things: `outcomes_bind`, `outcomes_ret`, and the observations
themselves.

---

## 1. Computation monads

| Type | Definition | File | Effects |
|---|---|---|---|
| `prog S A` | `stateT S (optionT (itree void1)) A` | `Prog.v` | state, exceptions, divergence (deterministic) |
| `ndprog S A` | `stateT S (optionT SetM) A` | `NonDetProg.v` | state, nondeterminism, **exceptions** |
| `nddprog S A` | `stateT S (optionT SetM) A` | `NonDetDivProg.v` | state, nondeterminism, **divergence** |
| `nditprog S A` | `stateT S (optionT (optionT SetM)) A` | `NonDetItProg.v` | state, nondeterminism, exceptions **and** divergence |

`ndprog` and `nddprog` share a carrier and differ only in the *reading* of the
distinguished outcome `None`: an exception in the first, divergence in the
second. Nothing in the type distinguishes them; what fixes the meaning is which
operations are offered. `NonDetProg.v` supplies `MonadExc` (`raiseP`/`catchP`);
`NonDetDivProg.v` deliberately supplies none, and offers `divergeD`,
`mayDiverge` and `orD` instead. `None` is absorbing under `bind` either way,
which is exactly the propagation rule divergence needs, so the monad structure
is identical.

Only `nditprog` can distinguish the two effects, via its second `optionT`.

## 2. The SP specification monads

Predicate transformers `(S -> Prop) -> Outcome -> Prop`, carved into four
monads by four healthiness conditions. **The bare transformer type is not a
monad**; only these subsets are.

| Monad | Carrier condition | Equivalent healthiness class | Reading of a relation `R` |
|---|---|---|---|
| `ASPProgSP` | `SingletonProg` | strict, universally disjunctive | `∃s ∈ pre, R s r` (angelic) |
| `DSLPProgSP` | `MSingletonProg` | terminating, universally conjunctive | `∀s, R s r → pre s` (demonic, liberal) |
| `DSPProgSP` | `StrictProg ∧ ConjunctiveProg` | **strict conjunctive** | `R⁻¹(r) ≠ ∅ ∧ R⁻¹(r) ⊆ pre` |
| `ASLPProgSP` | `TerminatingProg ∧ DisjunctiveProg` | **terminating disjunctive** | `R⁻¹(r) = ∅ ∨ pre ∩ R⁻¹(r) ≠ ∅` |

Two files, differing only in the outcome type:

| File | Outcome index | Contents |
|---|---|---|
| `SPSpecMonads.v` | `option (A * S)` | all four monads, laws, orders, comparison targets |
| `SPSimplerSpecMonads.v` | `A * S` (module `StSP`) | the same, for a plain stateful outcome |

Each monad comes with `ret`, `bind`, `Monad`, `Eq1`, `Eq1Equivalence` and
`MonadLawsE` (all four laws). `retDSPProg`/`bindDSPProg` are the conjunction of
the ASP and DSLP parts; `retASLPProg`/`bindASLPProg` the disjunction — see
`dsp_split` / `aslp_split` and the `aspPart*` / `dslpPart*` projections.

**Why DSP and ASLP need machinery the other two don't.** Reading a relation as
an ASP is monotone in the relation and as a DSLP antitone, so those two orders
*are* relation inclusion. DSP and ASLP are neither monotone nor antitone
(`dspOf_not_monotone` / `dspOf_not_antitone` and duals), so their `bind` cannot
be a forward pass over the precondition. It instead **recovers** each argument's
relation by probing at two constant preconditions, composes the relations, and
re-reads — see `dsp_recov` / `aslp_recov` and the `*_carrier` bridges. Both
carriers are stated as healthiness conditions; `dsp_carrier` / `aslp_carrier`
prove these equivalent to the fixed-point form the proofs use.

### Shared orders and comparison targets (`Section SpecOrders`)

At the end of `SPSpecMonads.v`, all computation-monad-independent:

- `approxKind` (`Under` / `Over`)
- orders `ordProgSP`, `ordProgASP`, `ordProgDSLP`, `ordProgDSP`, `ordProgASLP`,
  and the single-precondition variants `ordProgASPAt`, `ordProgDSLPAt`
- the **two** raw targets `pp2_over` / `pp2_under` — all eight per-monad
  instances had identical bodies, so there is one pair
- monotonicity `aspMono` / `dslpMono` / `dspMono` / `aslpMono`, one per
  healthiness condition
- twelve generic characterizations `gen_*` — eight raw, four in-monad

The `gen_*` theorems are stated for an **arbitrary** `w` in the relevant monad.
Each observation file obtains its own version by `exact`, since
`tripleASP prog Over pre post` is *definitionally* the left-hand side.

### In-monad characterizations

Only two of the eight triple directions are relation inclusions, and only those
work with the global order and no side condition:

| | `Over` | `Under` |
|---|---|---|
| ASP | `ordProgASP obs (tASPover …)` — global | `ordProgASPAt pre (tASPunder …) obs` — needs `∃s, pre s` |
| DSLP | `ordProgDSLPAt pre obs (tDSLPover …)` — needs `∃s, ¬pre s` | `ordProgDSLP (tDSLPunder …) obs` — global |
| DSP / ASLP | none | none |

`Over` always compares `obs ⊑ target`, `Under` always `target ⊑ obs`. The two
side conditions are forced by the healthiness conditions themselves
(`asp_bot`: every ASP is `False` at `⊥`; `dslp_top`: every DSLP is `True` at
`⊤`) and are not removable. DSP and ASLP have no in-monad target in either
direction, because their orders are not relation inclusion at all.

## 3. Observations

An observation maps a computation monad into the spec monads. Everything
downstream — monad-morphism theorems, triples, the taxonomy — follows from
`outcomes_bind` and `outcomes_ret`, whose case count tracks the effect layers.

| File | Source | Target | Divergence visible in specs? |
|---|---|---|---|
| `Observation.v` | `prog` | old-style transformers | — (deterministic) |
| `NonDetObservation.v` | `ndprog` | old-style transformers | n/a (exception reading) |
| `NonDetItObservation.v` | `nditprog` | old-style transformers | no |
| `SPNonDetItObservations.v` | `nditprog` | `SPSpecMonads` | **no** — reads the terminating slice |
| `SPNonDetObservations.v` | `nddprog` | `SPSpecMonads` | **yes** — `None` is an ordinary outcome |
| `SPNonDetDivObservations.v` | `nddprog` | `SPSimplerSpecMonads` | **no** — reads the terminating slice |
| `WPNonDetItObservations.v` | `nditprog` | `ProgWP` | WP side: `obsDWP`/`obsAWP`/`obsDWLP`/`obsAWLP` |

The three "New" files are the current design. Note the deliberate contrast in
the last column:

- `SPNonDetItObservations.v` reads
  `unOptionT (unOptionT (runStateT m s)) (Some r)`; the outer `Some` discards
  the divergent outcome, so its transformers see exceptions but **not**
  divergence.
- `SPNonDetObservations.v` keeps `None` in the outcome type, so
  `getProgASP (obsASP m) pre None` asserts *"some `pre`-state may diverge"* and
  `getProgDSLP (obsDSLP m) pre None` *"every state that may diverge satisfies
  `pre`"*.
- `SPNonDetDivObservations.v` observes the same monad into the `A * S`-indexed
  spec monads, so divergence is projected away again: `divergeD` satisfies every
  `Over` triple vacuously.

`SPNonDetObservations.v` imports only `NonDetDivProg` and `SPSpecMonads` — no
sibling observation file. That is the intended shape for any new observation.

Each New file provides `obsASP` / `obsDSLP` / `obsDSP` / `obsASLP`, proofs that
each is a **monad morphism** (`obs*_ret` / `obs*_bind`), the `getProg*_obs*`
readings, the contrapositive pairs, `triple*` with their refinement forms and
`*DefEq` equivalences, and the `cc_*` / `ii_*` / `ci_*` taxonomy.

## 4. Supporting specification types

| File | Type |
|---|---|
| `WP.v`, `WPFacts.v` | `PureWP = (A -> Prop) -> Prop`, `ProgWP` — backward transformers |
| `WPred.v`, `WPredFacts.v` | `WPred`, `ProgWPred` |
| `Pred.v`, `PredFacts.v` | `Pred A B = A -> B -> Prop`, the relational arrow |
| `SPost.v`, `SPostFacts.v` | SP *arrows* `PureASPostArr` / `PureDSLPostArr` over `SPRecord` |
| `PrePost.v`, `RelPrePost.v`, `WPArr.v` (+ `*Facts.v`) | Hoare pairs, validators, reader-WP Kleisli arrow |
| `Galois.v` | Galois connections among `Pred`, `PrePost`, `WPArr`, `RelPrePost` |

`ProgFacts.v` provides the generic `optionT` / `stateT` monad-law instances the
other `*Facts.v` files chain through.

**`PrePost` is strictly bigger than every SP monad.** `snd` composed with any SP
reading is a monad morphism, but it forgets the precondition and no injective
map exists (proved for the pure case). What does hold is a Galois connection
with each SP monad; for ASP it is order-preserving and for DSLP order-reversing.

---

## 5. Directory layout

    Taxonomy/
      ├── (computation monads, spec monads, observations — see above)
      ├── OldSP/          the earlier reading-based SP presentation
      └── deprecated/     older iterations, excluded from the build

### `OldSP/`

`OldSPObservations.v` (2920 lines) and `OldIncorrectnessRewritingRules.v` (250)
hold the earlier presentation of the SP side, superseded by `SPSpecMonads.v` +
`SPNonDetItObservations.v` but **not** redundant. It is the only place with:

- the **additive / multiplicative** SP monads — `AdditiveSP`,
  `MultiplicativeSP`, `PureSP`/`PureSPM`, `ProgSP`/`ProgSPM`, the product monad
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
`DSPProgSP` / `ASLPProgSP` are built by *recovering* relations rather than by a
forward pass, and nothing in the current files records that argument.

## 6. Build status

`_CoqProject` builds **clean from scratch**, and every `.v` file in this
directory (including `OldSP/`) is listed in it. Nothing is excluded.

### Why the example programs are split across three files

The example material was originally one file, which could not compile: the
old-style theorems (stated over `tripleSP` / `obsASP`) and the new-style ones
(over `tripleASP` / `tripleDSP`) used **the same ten names** — `progA_all`,
`progA_42`, `progA_43`, `progB_42`, `progB_not_None`, `progRet_asp_inc`,
`progRet_dsp_inc`, `example_incorrect_1`, `example_incorrect_2`,
`example_incorrect_unprovable`. They are now in separate files:

| File | Contents |
|---|---|
| `ExampleProgramDefs.v` | just the programs — `progA`, `progB`, `progRet`, `progEx`, `example_state` — plus `preEq0` / `postEq0`, which both presentations use |
| `ExamplePrograms.v` | the new-style (`tripleASP` / `tripleDSP`) and WP examples |
| `OldSP/OldExamplePrograms.v` | the old-style (`tripleSP` / `obsASP`) examples, the `OHearnExample` module, and the transported `m_*` worked examples |

`ExampleProgramDefs.v` is a leaf so that the observation files and the example
files can both use the programs without a cycle: `SPNonDetItObservations.v` and
`OldSP/OldSPObservations.v` state example lemmas about them, while the example
files prove triples using the observations those files define.

Two further blocks were relocated for the same reason:

- the transported `m_*` forms of O'Hearn's rules moved from
  `OldSP/OldSPObservations.v` into `OldSP/OldIncorrectnessRewritingRules.v`,
  since they `apply` the rules that file defines
- the worked examples `m_progA_under_42` / `m_progB_over_42` moved into
  `OldSP/OldExamplePrograms.v`, next to the `progA_42` / `progB_ASP_42` they
  discharge with

### One name clash remains, handled by qualification

`ExamplePrograms.v` keeps two old-style theorems (`progloom_triple_asp`,
`progloom_triple_asp_harder`) because they sit inside `Section
WithdrawExample`, whose other theorems are WP. That file therefore imports both
presentations, and `Over` / `Under` / `obsASP` are ambiguous — the old
`approximationKind` and the new `approxKind` both declare `Over` and `Under`.
The two old-style statements are written qualified
(`OldSPObservations.tripleSP`, `OldSPObservations.obsASP`,
`OldSPObservations.Under`); everything else resolves to the new definitions.

## 7. Stale build artifacts — safe to delete

`.vo` / `.vok` / `.vos` / `.glob` files whose `.v` source no longer exists:

    DijkstraCategory.*   Scratch{Adq,All,Arr,Awp,Bind,CE,Cmp,GC2,M,PT,Pick,Ret,Triple}.*
    Scratch_NDItCheck.glob

None are in `_CoqProject`, so nothing rebuilds them — but a stale `.vo` still
satisfies a `Require`, which is what masked a broken build during the
reorganisation. There are also `.v~` backups in `OldSP/`.

### `deprecated/`

Seven earlier iterations (`Observation.v`, `NonDetObservation.v`,
`NonDetItObservation.v`, `SPost.v`, `SPostArr.v`, `SPostFacts.v`,
`SPostFacts_arrowlaws.v`), excluded from `_CoqProject`. Ignore when grepping for
symbol references. This copy of `NonDetItObservation.v` is older than the
material in `OldSP/`.

### Superseded but still built

- **`NonDetObservation.v`** — nothing imports it. Superseded by
  `SPNonDetObservations.v`, which covers the same carrier with the four spec
  monads and full monad-morphism proofs. What it still uniquely has is the WP
  side (`obsDWP` / `obsAWP`).

- **`Observation.v`** — nothing imports it, but *not* superseded: there is no
  new-style observation file for the deterministic `prog`, and this is the only
  place with `obsWPCollapse` / `obsWLPCollapse`. It also holds the directory's
  single `Admitted` (line 575).

### Known duplication

`SPSpecMonads.v` and `SPSimplerSpecMonads.v` are near-copies differing only in
the outcome type, `bind`, and the four `comp_*` lemmas — everything else
transfers by re-indexing. Parameterising one development over an abstract
outcome functor plus a Kleisli `step` (with the three `comp_*` laws as
hypotheses) would share the bridges, carriers and targets and reduce each new
outcome type to one instance.

`SPNonDetItObservations.v` also still defines `pp2asp_over'` / `pp2dslp_under'`,
which duplicate `tASPover` / `tDSLPunder` in `SPSpecMonads.v`.

---

## Dependency graph (current files)

```
Prog ─────► ProgFacts ──► (generic optionT / stateT laws, reused everywhere)
NonDetProg ──► NonDetItProg
           └─► NonDetDivProg

SPSpecMonads  (standalone: four SP monads, laws, orders, pp2 targets)
     │  └──► SPSimplerSpecMonads        (same over A * S)
     │
     ├──► SPNonDetObservations          (nddprog,  divergence visible)
     ├──► SPNonDetDivObservations       (nddprog,  terminating slice) [via SPSimplerSpecMonads]
     └──► SPNonDetItObservations        (nditprog, terminating slice)
                └──► IncorrectnessRewritingRules

ExampleProgramDefs   (leaf: the programs + preEq0/postEq0)
     ├──► SPNonDetItObservations
     ├──► OldSP/OldSPObservations
     ├──► ExamplePrograms                (new-style + WP examples)
     └──► OldSP/OldExamplePrograms       (old-style examples)

WPNonDetItObservations  (nditprog → ProgWP; the WP half of the old file)
     └──► OldSP/OldSPObservations
                └──► OldSP/OldIncorrectnessRewritingRules
                          └──► OldSP/OldExamplePrograms

WP / WPred / Pred / SPost / PrePost / RelPrePost / WPArr ──► Galois
Observation, NonDetObservation                        (older observation style)
```
