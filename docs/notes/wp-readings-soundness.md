# To prove: each WP reading lands in its healthiness class

Status: done, in `Verification/DivNonDet/HealthyReadings.v` and
`Verification/DivNonDetSt/HealthyReadings.v` (with the converse: every
element of a variant is a reading), for contribution 3 ("monad morphisms from the base computation monad
into our eight *wp* and *sp* monads").

## The situation

- [WP/WPVariants.v](../../Code/WP/WPVariants.v) defines four classes of
  monotone WP transformers by healthiness, and their monads as submonads of
  `WPure`:

  | Monad | Health record | Conditions |
  |---|---|---|
  | `AWP`  | `awp_health`  | `wpure_mono`, `wpure_strict`, `wpure_disjunctive` |
  | `DWLP` | `dwlp_health` | `wpure_mono`, `wpure_terminating`, `wpure_conjunctive` |
  | `DWP`  | `dwp_health`  | `wpure_mono`, `wpure_strict`, `wpure_conjunctive` |
  | `AWLP` | `awlp_health` | `wpure_mono`, `wpure_terminating`, `wpure_disjunctive` |

  Each comes with its inclusion `toWPure : WPSub h ~> WPure` (a monad
  morphism: same `ret` and `bind`), and with state `toWSt : WPSubSt h S ~> WSt S`.

- [Verification/DivNonDet/Morphisms.v](../../Code/Verification/DivNonDet/Morphisms.v)
  defines the four readings of a computation as monad morphisms into the
  ambient monad, not into the classes:

  ```coq
  dwpPure  := demonicWP False   (* every outcome good, divergence bad  *)
  dwlpPure := demonicWP True    (* every outcome good, divergence good *)
  awpPure  := angelicWP False   (* some outcome good, divergence bad   *)
  awlpPure := angelicWP True    (* some outcome good, or one diverges  *)
  ```

  So the names AWP, DWLP, DWP, AWLP are justified only by the paper's
  prose: nothing proves that the angelic total reading of a program is an
  element of `AWP`.

```
divndNE ──dwpPure──▶ WPure
   ╲                   ▲
    ╲  (to prove)      │ toWPure
     ╲───────────▶ DWP = WPSub dwp_health
```

## Statements (base setting)

For every `A` and `d : divndNE A`:

```coq
Lemma dwpPure_healthy  : dwp_health  A (getWPure (dwpPure d)).
Lemma dwlpPure_healthy : dwlp_health A (getWPure (dwlpPure d)).
Lemma awpPure_healthy  : awp_health  A (getWPure (awpPure d)).
Lemma awlpPure_healthy : awlp_health A (getWPure (awlpPure d)).
```

Monotonicity is already proved (`demonic_mono`, `angelic_mono`). What each
remaining condition needs, with `demonic div d Q = ∀ oa ∈ outcomes d, …` and
`angelic div d Q = ∃ oa ∈ outcomes d, …` (`None` standing for divergence):

| Reading | Condition | Argument |
|---|---|---|
| `dwp`  | strict | `d` has an outcome (the `NE` of `divndNE`); at it `⊥` fails, whether a result (`Q := ⊥`) or divergence (`div = False`) |
| `dwp`, `dwlp` | conjunctive | `∀` commutes with `∀`; the divergence case `div ↔ ∀ i, div` needs the index type inhabited, which the definition provides |
| `dwlp` | terminating | `⊤` holds at every result, and `div = True` |
| `awp`  | strict | an existential over `⊥` results with `div = False` is false |
| `awp`, `awlp` | disjunctive | `∃` commutes with `∃`; the divergence case `div ↔ ∃ i, div` needs the index type inhabited |
| `awlp` | terminating | `d` has an outcome, and `⊤` / `div = True` holds there |

## Packaging

From each lemma, the corestriction

```coq
Definition dwpPure_DWP {A} (d : divndNE A) : DWP A := exist _ (getWPure (dwpPure d)) (dwpPure_healthy d).
```

with `toWPure ∘ dwpPure_DWP = dwpPure`. It is a monad morphism
`divndNE ~> DWP`, because `toWPure` is injective and preserves and reflects
`ret` and `bind` (the submonad has `WPure`'s operations). Then:

- **With state.** `WPSubSt h S = stateT S (WPSub h)` and
  `dwpSt = stateT_map S dwpPure`, so `stateT_map S dwpPure_DWP` is a monad
  morphism `stdivndNE S ~> DWPSt S` lifting `dwpSt` through `toWSt`, by the
  generic `MonadMorphism_stateT`. Nothing new to prove per reading.
- **With state and exceptions.** Needs the variants there first: a generic
  `WPSubStExc h S := stateT S (optionT (WPSub h))` with its laws and orders
  (from `MonadLawsE_optionT` / `OrderedMonad_optionT`) and the named
  `AWPStExc` &c. `MonadTaxonomy.v` already uses this type inline
  (`MonadRelation_implies_WPSubStExc`). Then lift as with state.

Place: the lemmas in `Verification/DivNonDet/Morphisms.v` (next to the
readings), the lifts in `DivNonDetSt/Morphisms.v` and
`DivNonDetStExc/Morphisms.v`, the `StExc` variants in `WP/WPVariants.v`.
Add the new names to `Checks/PaperClaims.v` (contribution 3, Section 3.5).

## What it gives

- The WP nodes of Figure 1 become the targets of the program readings, as
  the paper reads them, with a theorem instead of a naming convention.
- WP triples and Dijkstra monads can be indexed by the variants (`DWP`, …)
  instead of `WPure`; the existing `OrderedMonad` instances of the variants
  already allow it.
- The SP side has no such gap: `aspPure` &c. land in `ASP` &c. by
  construction.

## Open questions

- **Completeness.** Is every element of `AWP` the `awpPure` of some
  computation (and likewise for the others)? Not needed for the above; would
  make the classes exactly the readings.
- **Naming.** The health records name the reading (`awp_health`); naming
  them by content (`strict_disjunctive`, …) and keeping `AWP` &c. for the
  monads would make the lemmas read "the angelic total reading is strict and
  disjunctive".
- **One definition.** The four conditions are defined four times
  (`SP/PredicateTransformerProperties.v`, `SP/SPostArr.v` aliases,
  `WP/WPVariants.v`, `SP/RawSP.v`); the WP ones are instances of the generic
  `StrictArr` &c. at output `unit` (bridged in `PTMonadTaxonomy/Carriers.v`,
  `sp_strict_at` &c.). See [docs/design.md](../design.md#12-known-duplication).
