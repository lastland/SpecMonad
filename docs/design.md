# Design notes

A long-form tour of the development: computation monads, the SP and WP
specification monads, the morphisms and triples, the DM4All monads and their
adjunctions, and the arrow/monad split. The directory guide is
[Code/README.md](../Code/README.md); the paper-to-code index is
[PAPER.md](../PAPER.md). Section numbers below are this document's, not the
paper's.

The organising principle is a dependency boundary:

> **Specification carriers do not depend on concrete computation monads.**
> Monad morphisms connect the two sides by interpreting computation outcomes.

`WP/`, `SP/` and `Relational/` use specification types, generic
infrastructure (`Lib/`) and library definitions. The computation side is one
base monad, `divndNE`, and its transformer stacks, under `Verification/`,
which is split by setting: `DivNonDet/` (`divndNE`), `DivNonDetSt/` and `DivNonDetStExc/` (its
two lifts), and `Generic/` for what is the same at every setting. Each
setting holds its computation monad, the morphisms out of it, their triples,
the triple diagram and the Dijkstra monads.

Start with the computation monads (§2), then choose a specification
presentation (§3–4 and §8) and the morphisms into it (§5). The
[context map](agents/context/README.md) provides shorter directory guides. Formulas
below describe carriers and readings; unless shown as complete declarations,
they are schematic rather than standalone Coq commands.

The five unary specification monads in §7 follow Kenji Maillard et al.,
[*Dijkstra Monads for All*](https://doi.org/10.1145/3341708) (ICFP 2019),
abbreviated **DM4all** below.

---

## 1. Directory layout

See [Code/README.md](../Code/README.md). Logical paths follow the
directories: `Incorrectness.WP.WPure`, `Incorrectness.Verification.MonadMorphisms.MonadMorphisms`,
and so on.

## 2. Computation monads

All computation monads are in one file, `Computation.v`. The base monad is
built in three steps:

| Step | Definition | Role |
|---|---|---|
| `SetM A` | `A -> Prop` | a set of outcomes |
| `divnd A` | `optionT SetM A`, i.e. `option A -> Prop` | a set of outcomes, `None` being divergence |
| `divndNE A` | `{ m : divnd A \| nonEmptyOutcomes m }` | the base monad: at least one outcome |

`divndNE` is the base of everything in `Verification/`. The other two computation
monads are monad transformers applied to it, so they are non-empty by
construction:

| Level | Monad | Outcomes from a start state |
|---|---|---|
| base | `divndNE A` | `option A`: a result, or `None` for divergence |
| state | `stdivndNE S A := stateT S divndNE A` | `option (A * S)` |
| state + exceptions | `stdivexcndNE S A := stateT S (optionT divndNE) A` | `option (option (A * S))`: outer `None` is divergence, `Some None` an exception |

Besides the three monads the file has the choice, divergence, raise and pick
operations of the stacks, and the outcome lemmas `outSt_*` / `outStExc_*`.
`Verification/DivNonDet/Morphisms.v` imports it.
`TransformerLaws.v` proves the `optionT` / `stateT` laws for any
base monad, and lifts orders (`OrderedMonad_stateT`, ...) and monad morphisms
(`MonadMorphism_stateT`, ...) through them.

Non-emptiness matters for the four demonic-to-angelic WP implications: an
empty outcome set would satisfy every demonic triple vacuously. It is part of
the carrier, so no theorem carries it as a hypothesis.

## 3. The SP specification monads

Four healthiness conditions select the SP monads from the raw transformer
type `(X -> Prop) -> Y -> Prop`. The raw type alone does not justify the
sequencing laws: `SPostMonad.v` contains a counterexample to associativity for
the weaker stateful Kenji-style carrier and its proposed bind.

| Monad | Healthiness, besides monotone | Reading of a relation `R` |
|---|---|---|
| ASP | strict, disjunctive | `∃x ∈ pre, R x y` (angelic) |
| DSLP | terminating, conjunctive | `∀x, R x y → pre x` (demonic, liberal) |
| DSP | strict, conjunctive | `R⁻¹(y) ≠ ∅ ∧ R⁻¹(y) ⊆ pre` |
| ASLP | terminating, disjunctive | `R⁻¹(y) = ∅ ∨ pre ∩ R⁻¹(y) ≠ ∅` |

The carriers are the binary arrows `ASPArr`, `DSLPArr`, `DSPArr`, `ASLPArr` of
`SP/SPostArr.v` (§8) and their state and state-over-option stacks. One
file per monad fixes the arrow's input to `unit`:

| File | Without state | State | State + exceptions |
|---|---|---|---|
| `ASPMonad.v` | `ASP` | `ASPSt S` | `ASPStExc S` |
| `DSLPMonad.v` | `DSLP` | `DSLPSt S` | `DSLPStExc S` |
| `DSPMonad.v` | `DSP` | `DSPSt S` | `DSPStExc S` |
| `ASLPMonad.v` | `ASLP` | `ASLPSt S` | `ASLPStExc S` |

Each monad takes `ret`, `bind` and its laws from `Lib/Arrow/ArrowMonad.v`, and
comes with a runner on state preconditions (`getASPSt`, `getDSPStExc`, …), a
constructor from a relation (`aspOfRelSt`, `dspOfRelStExc`, …) and the
pointwise order on readings (`ordASP`, `ordASPSt`, `ordASPStExc`, …). An
element is determined by the relation it denotes; the relation of a DSP or
ASLP element is recovered classically.

### Which of them are specification monads

| Monad | Without state | State | State + exceptions |
|---|---|---|---|
| ASP | `OrderedMonad_ASP` | `OrderedMonad_ASPSt` | `OrderedMonad_ASPStExc` |
| DSLP | `OrderedMonad_DSLP` | `OrderedMonad_DSLPSt` | `OrderedMonad_DSLPStExc` |
| DSP | `OrderedMonad_DSP` | **no**: `not_OrderedMonad_DSPSt` | **no**: `not_OrderedMonad_DSPStExc` |
| ASLP | `OrderedMonad_ASLP` | **no**: `not_OrderedMonad_ASLPSt` | **no**: `not_OrderedMonad_ASLPStExc` |

The order is always the monad's own pointwise order. The four failures are at
Boolean state, and in the first argument of `bind` alone: one command returns
only from `false`, another preserves both states, and their common
continuation resets the state to `false`. A DSP or ASLP assertion bounds the
relation it denotes from both sides, so enlarging the first argument can
shrink what `bind` asserts. The monad laws still hold.

No other bind repairs this. `dsp_arbitrary_bind_impossible` and
`aslp_arbitrary_bind_impossible` take an arbitrary
`beta : M bool -> (bool -> M unit) -> M unit` on Boolean state and show that
the left-identity law for the monad's return and monotonicity in the first
argument are jointly unsatisfiable. The proofs use only that the result of
`beta` is in the carrier.

### Why DSP and ASLP collapse without state

Without state the precondition is one proposition, not a set of independently
chosen initial states. For an inhabited inverse image, requiring every
predecessor to satisfy that proposition is the same as requiring some
predecessor to do so. So at input `unit` the DSP and ASP healthiness
conditions cut out the same transformers, and likewise ASLP and DSLP.
`dsp_to_asp` / `asp_to_dsp` and `aslp_to_dslp` / `dslp_to_aslp` are the
identity on transformers, mutually inverse, and preserve `ret`, `bind` and the
orders. `OrderedMonad_DSP` and `OrderedMonad_ASLP` are the orders of ASP and
DSLP pulled back along them (`OrderedMonad_pullback`).

### The same base monads, defined directly

Each of the four files ends with the stateless monad written down directly,
with no arrow, on the raw transformer type `SPPure A = Prop -> A -> Prop` of
`SP/RawSP.v`:

| Direct monad | Carrier condition | `bind m k` at `p`, `b` |
|---|---|---|
| `ASPSP` | `Singleton`: `w p a <-> p /\ w True a` | `exists a, k a (m p a) b` |
| `DSLPSP` | `MSingleton`: `w p a <-> p \/ w False a` | `forall a, k a (m p a) b` |
| `DSPSP` | strict and conjunctive | `ASPSP`'s, transported |
| `ASLPSP` | terminating and disjunctive | `DSLPSP`'s, transported |

At a `Prop` precondition `Singleton` is the same as strict and disjunctive
(`join_iff_singleton`), and as the DSP condition
(`strict_conj_iff_singleton`); dually for `MSingleton`
(`meet_iff_msingleton`, `term_disj_iff_msingleton`).

Each direct monad is the same monad as the arrow-derived one. A proposition
is a predicate on `unit`, so a transformer on `Prop` preconditions is one on
`unit -> Prop` preconditions read at `tt`:

| Maps | Morphism theorems | Round trips |
|---|---|---|
| `aspsp_to_asp` / `asp_to_aspsp` | `aspsp_to_asp_morphism`, `asp_to_aspsp_morphism` | `aspsp_to_asp_to_aspsp`, `asp_to_aspsp_to_asp` |
| `dslpsp_to_dslp` / `dslp_to_dslpsp` | `dslpsp_to_dslp_morphism`, `dslp_to_dslpsp_morphism` | `dslpsp_to_dslp_to_dslpsp`, `dslp_to_dslpsp_to_dslp` |
| `dspsp_to_dsp` / `dsp_to_dspsp` | `dspsp_to_dsp_morphism`, `dsp_to_dspsp_morphism` | `dspsp_to_dsp_to_dspsp`, `dsp_to_dspsp_to_dsp` |
| `aslpsp_to_aslp` / `aslp_to_aslpsp` | `aslpsp_to_aslp_morphism`, `aslp_to_aslpsp_morphism` | `aslpsp_to_aslp_to_aslpsp`, `aslp_to_aslpsp_to_aslp` |

The maps are mutually inverse, preserve `ret` and `bind`, and preserve and
reflect the orders (`ordASPSP_aspsp_to_asp`, `ordASP_asp_to_aspsp`, and
likewise). So the direct monads are specification monads too
(`OrderedMonad_ASPSP` and its three companions). The ASP statements are
axiom-free. Only the stateless level has a direct definition; with state and
with exceptions the monads are the arrow stacks.

### Pre- and postconditions as elements

The elements that a pair of a pre- and a postcondition determines are the
indices of §9: `aspOver`, `dslpUnder`, `aspUnder`, `dslpOver` in
`Verification/Generic/DijkstraMonad.v`.

## 4. The WP specification monads

`WP/WPure.v` defines three WP monads and their refinement
orders:

```coq
WPureT A   := (A -> Prop) -> Prop                    (* raw; used by GaloisConnections/WPArr.v *)
wpure_mono f := forall p q, (p ⊆ q) -> f p -> f q
WPure  A   := { f : WPureT A | wpure_mono f }        (* the monad *)

WSt    S   := stateT S WPure                         (* W^St     *)
WStExc S   := stateT S (optionT WPure)                (* W^StExc  *)
```

After applying the stack runners and `getWPure`, `WSt` takes an initial state
and a postcondition on `A * S`. `WStExc` instead takes a postcondition on
`option (A * S)` and supplies `MonadExc`. These are the shapes of the
evaluators, not equalities of the bundled carriers with unrestricted
functions.

For `WPure`, the file defines `ret`, `bind`, and pointwise-iff `Eq1`, and
proves `MonadLawsE` directly. The two stacks inherit their laws from the
`Eq1`-generic `optionT` and `stateT` instances in
`Lib/Monad/TransformerLaws.v`.
`Coercion getWPure : WPure >-> Funclass` keeps application (`w post`) working
through the subset type.

The adjunction and `Proper_bind` proofs use the bundled monotonicity. Each WP
morphism therefore supplies a monotonicity proof when constructing a `WPure`
value (`demonic_mono`, `angelic_mono` in `Verification/DivNonDet/Morphisms.v`).

All three WP orders live in `WP/WPure.v`. Each stack order is a generic
lift of **reverse implication** from `WP_le`; the formulas below omit runners:

| order | on | meaning of `w1 ⊑ w2` |
|---|---|---|
| `WP_le` (+ `WP_le_PreOrder`) | `WPure` | `forall post, w2 post -> w1 post` |
| `ordWSt` | `WSt S` | `forall s post, w2 s post -> w1 s post` |
| `ordWStExc` | `WStExc S` | `forall s post, w2 s post -> w1 s post` |

The lifts preserve argument order: a transformer that yields pointwise weaker
preconditions is lower in the refinement order. The DM4all adjunctions and
the identification of WP triples with Dijkstra typings use these reverse
orders: an `Under` triple is `θ m ⊑ wpUnder pre post` and an `Over` triple
`wpOver pre post ⊑ θ m` (`Verification/Generic/DijkstraMonad.v`).

**`GaloisConnections/WPArr.v` uses the raw carrier `WPureT`**, not `WPure`. Its `ArrowEq`
is Leibniz equality. Some laws hold by conversion; laws involving products and
sums also use functional extensionality. This equality contract differs from
`WPure`'s pointwise logical equivalence.

## 5. Monad morphisms and triples

[`Lib/Monad/OrderedMonad.v`](../Code/Lib/Monad/OrderedMonad.v) defines a monad morphism
(`MonadMorphism`: properness, and preservation of `ret` and `bind` up to the
target's equality). `Verification/Generic/Triple.v` defines the triple, once (binders
abbreviated here):

```coq
Inductive approxKind := Under | Over.

Definition pt_holds (r : PTReading X Y) (k : approxKind) P Q : Prop :=
  match r, k with
  | Forward t,  Under => forall y, Q y -> t P y     (* post ⊆ sp pre *)
  | Forward t,  Over  => forall y, t P y -> Q y     (* sp pre ⊆ post *)
  | Backward t, Under => forall x, P x -> t Q x     (* pre ⊆ wp post *)
  | Backward t, Over  => forall x, t Q x -> P x     (* wp post ⊆ pre *)
  end.

Definition triple θ {Hθ : IsMonadMorphism θ} m k P Q := spec_holds (θ _ m) k P Q.
```

A `SpecReading` instance says how an element of a specification monad is
read, forward (SP) or backward (WP), and what its pre- and postconditions are
predicates on; the instances for `WPure`, ASP, DSLP, DSP, ASLP and their
stacks are in the second part of `Triple.v`. `approxKind` is the only kind
inductive of the project. `spec_holds w k P Q` is the judgement on an
element. A statement that mentions `triple θ` depends on the assumptions of
`θ`'s instance. `triple`
accepts a map `θ` only if it has an `IsMonadMorphism` instance, which bundles
the proof that `θ` is a `MonadMorphism`; the types of `P` and `Q` are those of
`θ`'s target. The four cases of `pt_holds`, at the four WP and the four SP
readings, are the sixteen triples. `Under` means the transformer's value is in
the conclusion on both sides, so a WP `Under` triple is the correctness-like
one and an SP `Under` triple the incorrectness-like one.

A statement that mentions `triple θ` depends on the assumptions of `θ`'s
instance, that is, of its target monad and of its return/bind laws.

### The eight readings, lifted — `Verification/DivNonDet/Morphisms.v`

Each reading is defined once, over the non-empty base `divndNE`, and lifted.
They are monad morphisms and are not called observations: an effect
observation goes into a specification monad, which the DSP and ASLP targets
are not. A map is named by its reading and its level: `dwpPure`, `dwpSt`,
`dwpStExc`, and likewise for `dwlp`, `awp`, `awlp`, `asp`, `dslp`, `dsp`,
`aslp`.

| Level | Computation | WP target | SP targets |
|---|---|---|---|
| base | `divndNE` | `WPure` | `ASP`, `DSLP`, `DSP`, `ASLP` |
| state | `stateT S divndNE` | `WSt S` | `ASPSt S` and the other three |
| state + exceptions | `stateT S (optionT divndNE)` | `WStExc S` | `ASPStExc S` and the other three |

- **WP.** The four base maps are monad morphisms `divndNE ~> WPure`.
  `MonadMorphism_stateT` and `MonadMorphism_optionT`
  (`Lib/Monad/TransformerLaws.v`) lift them, and the triple of a
  lifted morphism is the base triple at every start state
  (`triple_dwpSt`, `triple_dwpStExc`, and so on, in
  `Verification/DivNonDetSt/Triples.v`).
- **SP.** A base arrow morphism out of `Rel` (`SP/SPostArrEquiv.v`) is
  lifted by the arrow transformers and applied to the relation between start
  states and terminating outcomes; `arrow_morphism_monad`
  (`Lib/Arrow/ArrowMorphism.v`) makes it a monad morphism. The triple at every
  level is one judgement on the base arrow, re-indexed (`triple_aspSt`, and so
  on, in `Verification/DivNonDetSt/Triples.v`). An SP triple at the state level is not a family of base triples, and
  at unit input the four SP readings are two.

The lifted SP morphism theorems inherit the functional extensionality of the
arrow transformers' law packages. The same statements are also proved through
the relations denoted (`aspSt_morphism_rel`, and so on), and the
`IsMonadMorphism` instances use those: triples through the ASP and DSLP
morphisms are closed, and those through DSP and ASLP use excluded middle. See
the [Triples context](agents/context/Verification.md).

## 6. The triple diagram — `Verification/DivNonDetSt/TriplesTaxonomy.v`

Figure 5 of Lena Verscht and Benjamin Lucien Kaminski's
[*A Taxonomy of Hoare-Like Logics: Towards a Holistic View using Predicate
Transformers and Kleene Algebras with Top and Tests*](https://doi.org/10.1145/3704896)
(POPL 2025), for one computation, a precondition on start states and a
postcondition on results:

| Edges | Count | From |
|---|---|---|
| WP implications | 8 | inclusions between the four base readings of one `divndNE` element, lifted start state by start state |
| WP contrapositives | 4 | the same, with excluded middle |
| SP implications | 8 | the four elements of one relation, at arbitrary indices |
| SP contrapositives | 4 | the same, with excluded middle |
| Galois (`b ⊆ dwlp(c)` iff `asp(b) ⊆ c`; `awp(c) ⊆ b` iff `c ⊆ dslp(b)`) | 2 | the base Galois relations between the terminating outcomes and a WP reading |

All 26 are proved twice: for `m : stateT S divndNE A` with a postcondition on
`A * S` (`dwp_under_dwlp_under`, ...), and for
`m : stateT S (optionT divndNE) A` with a postcondition on `option (A * S)`
(the same names with `_exc`). No edge has a side condition.

## 7. The DM4all specification monads and their adjunctions

The five standalone base specification monads port the implementations in
`theories/sprop/SpecificationMonads.v`, the artifact file accompanying
[*Dijkstra Monads for All*](https://doi.org/10.1145/3341708) (ICFP 2019).
Each is unary (`Type -> Type`) and has `Monad` and `MonadLawsE`. Their `Eq1`
compares underlying propositions by logical equivalence, so the law statements
do not require equality of bundled proofs. Assumptions should be checked for
the particular theorem, not inferred from a file's imports or this summary.

| file | module | carrier | DM4all name |
|---|---|---|---|
| `Relational/PredMonad.v` | `PredM` | `Pred A = A -> Prop` | `PredOM` |
| `GaloisConnections/PrePostMonad.v` | `PPM` | `PrePost A = Prop * (A -> Prop)` | `PPSpecMonad` |
| `SP/SPostMonad.v` | `SPM` | `SPost A = { f : forall p, A -> Over p \| sp_mono f }` | `ForwardPredTransformer` |
| `WP/WPure.v` | — | `WPure A = { f : (A -> Prop) -> Prop \| wpure_mono f }` | `WPure` |
| `GaloisConnections/RelPrePostMonad.v` | `RPPM` | `RelPrePost X = { r : forall p, (X -> Assuming p) -> Assuming p \| rpp_mono r }` | `MRSpec` |

The carrier constraints explain two important proof steps. `Over p` stores a
proposition that implies `p`; the `SPost` associativity proof uses that implication
to recover an intermediate witness. `Assuming p` stores a proposition `q` with
`q <-> (p -> q)`; `ab_close` discharges the leading assumption in the
`RelPrePost` left-unit proof.

Each of the five files also defines its monad's refinement order, with its
`PreOrder` instance and the proof that it makes the monad a specification
monad:

| file | order | specification monad |
|---|---|---|
| `PredMonad.v` | `Pred_le`; `ordPredStExc` on the stack | `OrderedMonad_Pred`, `OrderedMonad_PredStExc` |
| `PrePostMonad.v` | `PP_le` | `OrderedMonad_PrePost` |
| `SPostMonad.v` | `SP_le` | `OrderedMonad_SPost` |
| `WP/WPure.v` | `WP_le`; `ordWSt`, `ordWStExc` on the stacks | `OrderedMonad_WPure`, `OrderedMonad_WSt`, `OrderedMonad_WStExc` |
| `RelPrePostMonad.v` | `MR_le` | `OrderedMonad_RelPrePost` |

`ordPredStExc` is the pointwise lift of `Pred_le` and runs forward (more
outcomes is bigger); `ordWSt` and `ordWStExc` are the lifts of `WP_le` and run
backward (a weaker precondition is bigger). The stack proofs are the generic
transformer lifts of `TransformerLaws.v`.

`GaloisConnections/BaseGaloisConnections.v` uses those orders to establish
DM4all's `Section Adjunctions` results:

| theorem | statement |
|---|---|
| `pred_pp_adjunction` | `PP_le (pred2pp post) pp <-> Pred_le post (pp2pred pp)` |
| `wp_pp_under_adjunction` | `PP_le pp (wp2pp_under w) <-> WP_le (pp2wp_under pp) w` |
| `wp_pp_over_adjunction` | `PP_le (wp2pp_over w) pp <-> WP_le w (pp2wp_over pp)` |
| `wp_mr_adjunction` | `WP_le w (mr2wp r) <-> MR_le (wp2mr w) r` |
| `sp_pp_adjunction` | `PP_le (sp2pp sp) pp <-> SP_le sp (pp2sp pp)` |
| `sp_mr_adjunction` | `MR_le (sp2mr sp) mr <-> SP_le sp (mr2sp mr)` |

plus the unit/counit round trips, each obtained by instantiating an adjunction
at reflexivity (`pp2sp_sp2pp_loop` / `sp2pp_pp2sp_loop` are DM4all's).
`wp_pp_over_adjunction` is a second adjunction between `PrePost` and `WPure`,
with `WPure` on the left; it is not DM4all's and is the only classical one.

`WP_le` and `MR_le` are *reversed* — a weaker demand is lower.

`pp2sp` uses an impredicative intersection: `pp2spBase` quantifies over every
`SPost` above `fun p a => p /\ PPM.post pp a`. Its underlying proposition
depends only on `PPM.post pp`, not on the pair's precondition. The theorem
`pp2sp01` compares it with the simpler candidate
`pp2sp0 pp = fun p a => p /\ (PPM.pre pp -> PPM.post pp a)`.

This adjunction does not supply an index for ASP `Under` triples. With state
no such index exists (`no_asp_under_index`, §9). The DM4all unary carrier and
the stateful ASP carrier have different contracts.

The file does *not* `Import PPM`: `PPM` binds `pre` and `post`, which would
capture the binders of the SP embeddings, so `PPM.pre` / `PPM.post` are written
throughout.

### Relation to `GaloisConnections/GaloisArr.v`

`GaloisConnections/GaloisArr.v` proves four binary connections: `Galois_Rel_PrePost`,
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
| `Pred` / `Rel` | `Relational/PredMonad.v` — `Pred A = A -> Prop` | `Relational/Rel.v` — `Rel A B = A -> B -> Prop` |
| `PrePost` | `GaloisConnections/PrePostMonad.v` — `PrePost A = Prop * (A -> Prop)` | `GaloisConnections/PrePostArr.v` |
| `SPost` | `SP/SPostMonad.v` — `SPost A` over `Over p` | `SP/SPostArr.v` — property-only `ASPArr`, `DSLPArr`, `DSPArr`, `ASLPArr`; `Relational/RelSPostArr.v` — four SP readings of the existing `Rel` carrier |
| `RelPrePost` | `GaloisConnections/RelPrePostMonad.v` — over `Assuming p` | `GaloisConnections/RelPrePostArr.v` |
| `WPure` / `WP` | `WP/WPure.v` | `GaloisConnections/WPArr.v` |

The five unary specification-monad files define their carriers **in terms of the result type alone**
(`Pred A = A -> Prop`), rather than fixing the input of a binary arrow.
`WPArr.v` reuses the raw carrier `WPureT`.
`PredicateTransformerProperties.v` defines binary SP healthiness
properties independently of the base-monad development.

The four public flavour monads instead consume the binary implementation in
`SP/SPostArr.v`, fixing the input and adding unary runners, orders, and
monad-specific results. `SPostArr.v` owns the raw `SPArrT` and the ASP and
DSLP carriers; `DSPASLPArr.v` the DSP and ASLP ones. Together they hold the
operations, normal forms, recovered relations, laws, binary stacks, and
arrow-level conversions. No monad file and nothing in `Relational/RelMonads.v`
is a dependency of these implementations. The SP dependency direction is
`Lib/` and `Relational/` → `SPostArr` → `DSPASLPArr` → the monad files →
`PTMonadTaxonomy/` → `Verification/`.

`Rel.v` separately owns the relation carrier, stacks, and congruence;
`RelSPostArr.v` owns their four SP readings and supporting facts.
`RelMonads.v` retains only unary relational monads, their return/bind facts,
and orders.

General arrow infrastructure lives in `Code/Lib/Arrow/`. `ArrowMonad.v` defines
the generic return/bind operations for `arr I` and proves their monad laws;
`ArrowApplyFacts.v` supplies the shared algebraic application and arrow
extensionality lemmas used by the monad and option-transformer proofs.
`ArrowMorphism.v` packages maps that respect the selected source and destination
equalities, proves operation preservation, and lifts the maps through option/state.

`RelArrowCoherence.v` derives complete core, choice, and application law
packages from relational operation contracts and `RelArrowEq`, which connects
the chosen arrow equivalence to pointwise relation equivalence. Its
relational-only helpers do not require equality reflection.

Its `rel_bind` / `relS_bind` normalize base and state bind. The `relO_comp`,
`relO_pure`, and `relO_first` lemmas handle option arrows; `relE_comp`,
`relE_pure`, `relE_first`, `relE_app`, and `relE_bind` handle state-over-option
arrows. These formulas use the existing `RelArrow`, `RelArrowChoice`, and
`RelArrowApply` dictionaries, without arrow-law premises or equality reflection.
Bind keeps the fixed input, threads the intermediate state, and propagates
`None` without a final state. The canonical relation-reading wrappers in
`SPostArr.v` specialize this shared normalization.

The retained `rel_state_option_pure` / `rel_state_option_bind` and
`ASP_rel_presentation` / `DSLP_rel_presentation` also expose the bundled
exact-equality interface for independent consumers; the direct-Rel equivalences
below do not use it. Concrete proofs retain the assumptions used to establish
their relational readings.

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
aliases and compact return/bind agreement proofs live in `Tests/`.
Production modules retain the compact Pred and RelPrePost operations used by
their mathematical consumers.

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

`Tests/ArrowMonadRegression.v` checks generic law resolution and a
counterexample: a lawful arrow whose application satisfies the old fixed-arrow
law but violates monad right identity. The stronger application contract
rejects it.

`Tests/SPostArrInfrastructure.v` checks core, choice, and application
laws for all four property-only flavours without importing the SP monad files.
Its semantic regressions distinguish DSP composition from raw transformer
composition and exercise binary state-over-option bind with a non-unit input.

`Tests/ArrowMonadInstances.v` collects the concrete monad,
`Eq1Equivalence`, and `MonadLawsE` dictionaries of the specification arrows
together with their compact relational `ret`/`bind` descriptions and agreement
facts. It checks the exact derived monad dictionary for `Rel`, the property-only
ASP/DSLP carriers, and the other specification arrows, using their selected
equalities. Base, option, state, and state-over-option checks include non-unit
inputs. The relational checks serve both `asp` and `dslp` readings; the readings
do not need separate monad dictionaries. Named concrete dictionaries are also
checked against the generic dictionary, with automatic law resolution under
their canonical equalities.
`Tests/ArrowTransformerInstances.v` holds the transformer-stack
resolution checks: the `optionRel` and relational state-over-option laws,
the monad-view `progRelM` / `nditRelM` stacks, and the double-option
application-law witnesses. Relational arrow-stack dictionaries resolve through
the generic transformers. The file also checks the definition of
property-only pointwise equality, automatic base core/choice/application law
resolution, and semantic `app_ext` and bind-continuation congruence for both
ASP and DSLP.
All three concrete test modules are in `_CoqProject`, so the normal build checks
them. The two instance-test modules register no helper instances. Explicit
generic applications check specialization; `:= _` checks automatic resolution.
The two named SP-stack law witnesses use explicit applications to pin the exact
dictionaries and avoid competing recursive option/state search paths.
`CanonicalSP` additionally checks
cross-API application and bind, pure/state clients, runner identity, and a state
update followed by propagated failure.

### Relational SP readings

[`Relational/RelSPostArr.v`](../Code/Relational/RelSPostArr.v) computes four SP readings of the
existing `Rel A B := A -> B -> Prop` carrier. **An arrow value is a relation**,
not a pair of a relation and a transformer or a new wrapper:

```text
asp    R P b = exists a, P a /\ R a b
dslp   R P b = forall a, R a b -> P a
dspOf  R P b = asp R P b /\ dslp R P b
aslpOf R P b = asp R P b \/ dslp R P b
```

`aspOf` / `dslpOf` are transparent aliases of `asp` / `dslp`. The module also
owns the readings' healthiness, recovery, inclusion, and operation facts.

ASP asks for some predecessor in the precondition; DSLP requires every
predecessor to satisfy it. At an unreachable output, ASP is false and DSLP is
vacuously true. This also holds when the input type is empty. Determinism alone
does not identify the readings: for the constant function `bool -> unit` and
precondition `eq true`, ASP holds at `tt`, but DSLP fails because `false` is
also a predecessor.

All four readings use `Arrow_Rel`, `ArrowChoice_Rel`, `ArrowApply_Rel`, and their
existing laws in [`Rel.v`](../Code/Relational/Rel.v). The selected equality remains
`Rel_eq`, namely `forall a b, R a b <-> R' a b`. The same `optionRel` and
`progRelArr` stacks serve all four readings; choosing a reading changes the
predicate transformer, not the relation, its operations, or its law packages.

`RelSPostArr.v` also retains `asp_inv` / `dslp_inv` and their recovery facts.
The reverse transformer round trips concern transformers in the image of the
respective reading, not arbitrary raw transformers. `dsp_asp_dslp` and
`aslp_asp_dslp` characterize the DSP and ASLP readings as the conjunction and
disjunction of ASP and DSLP over the same relation.

These results follow Lena Verscht and Benjamin Lucien Kaminski,
[*A Taxonomy of Hoare-Like Logics: Towards a Holistic View using Predicate
Transformers and Kleene Algebras with Top and Tests*](https://doi.org/10.1145/3704896),
POPL 2025. The article's Definitions 3.5 and 3.6 give the DSP and ASLP readings;
its §3.2.4 gives the conjunction/disjunction identities.

### Property-only SP arrows

`SP/PredicateTransformerProperties.v` defines `StrictArr`,
`TerminatingArr`, `ConjunctiveArr`, and `DisjunctiveArr` for
`(A -> Prop) -> B -> Prop`, following Ralph-Johan Back and Joakim von Wright,
*Refinement Calculus: A Systematic Introduction* (1997 draft, §16.1; published
1998). The [terminology source note](../Code/SP/PROPERTY_TERMINOLOGY.md#sources-and-verification-limits)
identifies the version consulted. Conjunctivity and disjunctivity preserve
arbitrary **nonempty** families. Strictness supplies empty-join preservation;
termination supplies empty-meet preservation. Here, termination means **top
preservation**, with its operational interpretation determined by the direction
of the transformer.

`SP/SPostArr.v` implements all four canonical carriers over
`SPArrT A B := (A -> Prop) -> B -> Prop`. Each stores only a transformer and
healthiness proofs, including explicit monotonicity:

| Carrier | Additional healthiness conditions |
|---|---|
| `ASPArr` | strict and disjunctive |
| `DSLPArr` | top-preserving and conjunctive |
| `DSPArr` | strict and conjunctive |
| `ASLPArr` | top-preserving and disjunctive |

The same module retains the ASP/DSLP compatibility aliases:

```coq
PureASPostArr A B := ASPArr A B.
PureDSLPostArr A B := DSLPArr A B.
```

The binary compatibility accessors are `SPostArr.getASP` and
`SPostArr.getDSLP`; distinguish them from the unary `ASPMonad.getASP` and
`DSLPMonad.getDSLP`. `arrASP` / `arrDSLP` alias `pureASP` / `pureDSLP`;
`arrASP_spec` / `arrDSLP_spec` expose their direct and universal images.
ASP/DSLP composition forwards the precondition:
`comp f g P = g (f P)`. Application satisfies these normal-form equivalences:

```text
appASP  P b <-> exists f, getASP  f (fun a => P (f,a)) b
appDSLP P b <-> forall f, getDSLP f (fun a => P (f,a)) b
```

DSP/ASLP sequencing instead recovers each argument's relation, composes its
ASP/DSLP readings, and recombines the results by conjunction/disjunction.
In particular, DSP composition is **not** raw forward transformer composition.

Canonical operation names such as `compASP` and `appASP` belong to `SPostArr`.
Compatibility dictionary names remain plain definitions over the canonical
instances, with no duplicate global registrations. All four carriers satisfy
`ArrowLaws`, `ArrowChoiceLaws`, and `ArrowApplyLaws`.
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
The canonical `aspRel` probes `fun x => x = a`, while `ASP_rel` probes `eq a`
(`fun x => a = x`). These singleton predicates are logically equivalent, not
definitionally equal; the proofs use predicate-iff bridges. The canonical and
compatibility DSLP recovered relations are definitionally identical.
All four canonical SP carriers instantiate the shared `RelArrow`,
`RelArrowChoice`, `RelArrowApply`, and `RelArrowEq` contracts in
`Lib/Arrow/RelArrowCoherence.v`. Those contracts supply their complete
core/choice/application law packages under pointwise transformer iff.
The ASP/DSLP normal forms and base law packages are constructive; exact bundled
equality remains available separately with extensionality. The separate
`dslpRel_probe` complement characterization is classical, as are DSP/ASLP recovery
and law packages. The relational carrier reuses its existing laws in `Rel.v`.
The generic transformers preserve both sets of laws algebraically.


`SPostArr.v` ends by separating the four classes on one relation,
`trueFromBoth : SPureArr bool bool`, whose output `true` is reached from both
inputs and whose output `false` from none. Its DSP reading is neither
top-preserving nor disjunctive (`dspOf_not_terminating`,
`dspOf_not_disjunctive`), its ASLP reading neither strict nor conjunctive
(`aslpOf_not_strict`, `aslpOf_not_conjunctive`), and its DSLP reading is not
disjunctive (`dslpOf_not_disjunctive`). So the DSP and the ASLP reading are
the transformer of no ASP arrow and of no DSLP arrow, and the DSLP reading of
no ASP arrow: `no_ASPArr_for_dsp`, `no_DSLPArr_for_dsp`, `no_ASPArr_for_aslp`,
`no_DSLPArr_for_aslp`, `no_ASPArr_for_dslp`. These say the readings are not
additive or multiplicative; they do not concern the DSP and ASLP monads or
their sequencing.

### Equivalence with `Rel`

[`SPostArrEquiv.v`](../Code/SP/SPostArrEquiv.v) relates property-only ASP and DSLP
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
`Lib/Arrow/ArrowMorphism.v`:

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
corresponding selected `arrow_eq`.

The option maps use `option_arrow_map`, and their morphism theorems use
`option_arrow_morphism`. The state-over-option maps apply `state_arrow_map`
to those option maps; their morphism theorems use the combined
`state_option_arrow_morphism`. For state-only lifts, apply `state_arrow_map`
and `state_arrow_morphism` directly.

Inverse and lift proofs use the existing core/choice/application laws under
the selected equality dictionaries. Inverse application uses `app_ext`; state
lifting uses the core `pure_proper` field. See the
[Lib contract](agents/context/Lib.md#contracts)
for each generic theorem's law requirements. The direct-Rel equivalences do
not reflect `Rel_eq` into ordinary equality or use Leibniz law dictionaries.

`ArrowEq_leibniz` and the property-only `ArrowLaws_*_leibniz` /
`ArrowChoiceLaws_*_leibniz` helpers remain independent APIs, not prerequisites
for these equivalences. `PureASPostArr_eq` / `PureDSLPostArr_eq` also remain
available to recover equality of bundled property-only arrows where needed.
Consult the [assumption audit](agents/context/Checks.md) for selected theorem
dependencies.

Checked clients live in `Tests/SPostArrExamples.v`; monad and
transformer instantiation checks live in `Tests/` too.

`Relational/OptionLoop.v` proves that `optionRel` cannot satisfy unrestricted
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

## 9. Examples, rewriting rules, Dijkstra monads

**Examples.** `Verification/DivNonDetStExc/Examples.v` defines `progA`, `progB`, `progRet`,
`progEx`, `example_state` (Example 3.1 of Peter W. O'Hearn's
[*Incorrectness Logic*](https://doi.org/10.1145/3371078), POPL 2020),
`progloom` and `progloom_harder` over `stateT S (optionT divndNE)`, and
verifies one triple for each of the sixteen kinds. The `progloom` theorems
contrast angelic *coverage* (`awpStExc` `Under`: from every start state some
run raises) with bug *presence* (`aspStExc` `Under`: the raise is reached from
some start state), over the same program and postcondition.

**Rewriting rules.** `Verification/DivNonDetSt/InCorrectnessPrinciples.v` states O'Hearn's
rules over the `aspSt` triples of a computation with state: the two symmetry
rules, the two rules of consequence, and the principles of agreement and
denial. The correctness-side rules also have a variant for the demonic
liberal WP triples `dwlpSt`
(`second_symmetry_rule_dwlp`, `second_imp_symmetry_rule_dwlp`,
`principle_of_agreement_dwlp`, `principle_of_denial_dwlp`), each obtained from
its ASP counterpart through the Galois edge of the diagram.

**Dijkstra monads.** `Verification/Generic/DijkstraMonad.v` gives, for any monad
morphism `θ : M ~> W` into a specification monad `(W, le)`,

```text
DM θ le w    =  { m : M A | le (θ m) w }
DMop θ le w  =  DM θ (flip le) w  =  { m : M A | le w (θ m) }
```

with `ret`, `bind`, weakening and lift, and DM4All's laws of a Dijkstra monad
(`DM_laws`, `DMop_laws`): the three monad laws and the three laws of
weakening, up to equality of the underlying computations (`DM_eq`). They hold
whenever the source monad is lawful, so for all twelve named monads
(`Ddwp_laws`, ...). A specification monad is still one
with its order flipped (`OrderedMonad_flip`), so `DMop` is the same
construction at the flipped order, not a second one. The WP, ASP and DSLP
morphisms of §5 have both at all three levels: the 18 `OrderedTarget`
instances name the natural order of each target and nothing else is supplied.
The WP targets carry the refinement order and its lifts, ASP and DSLP the
pointwise order of their transformers. DSP and ASLP are not specification
monads for their natural order (`not_OrderedMonad_DSPSt`,
`not_OrderedMonad_ASLPSt`), so their morphisms have no Dijkstra monad.

With state and exceptions the twelve Dijkstra monads have names: eight WP
ones, `Ddwp`, `Ddwlp`, `Dawp`, `Dawlp` and their `_op`, and four SP ones,
`Dasp`, `Ddslp` and their `_op`.

Triples are typings where the two say the same: a WP `Under` triple is a
typing in `DM` at `wpUnder pre post` and a WP `Over` triple one in `DMop` at
`wpOver pre post`, for all four WP readings; ASP `Over` is a typing in `DM`
at `aspOver`, and DSLP `Under` one in `DMop` at `dslpUnder`.

The two remaining SP kinds are not typings. A typing in `Dasp_op` at
`aspUnder pre post` says every start state in `pre` reaches every result in
`post` (`le_aspUnder`); the ASP `Under` triple asks for some start state per
result. `no_asp_under_index` shows no index at all has the triple as its
typings, and `no_dslp_over_index` the same for DSLP `Over`: typings are
inclusions of relations, so they are closed under intersection, and these
triples are not. Without state there is one start point and the ASP `Under`
triple is a typing (`triple_under_aspPure`, for a precondition that holds).

`Verification/DivNonDetStExc/DijkstraExamples.v` types one program in each of the eight WP
Dijkstra monads, in `Dasp` and in `Ddslp_op`; gives a typing in `Dasp_op` and
one in `Ddslp` that say more than their triples; gives an ASP `Under` and a
DSLP `Over` triple that are not typings (`progloom_harder`); and types a
stateless program at ASP `Under`. See the
[Dijkstra context](agents/context/Verification.md).

## 10. Build status

[`_CoqProject`](../Code/_CoqProject) lists the normal build's sources. The
[root README](../README.md#build) gives the build commands, and the
[opam manifest](../Code/coq-spec-monad.opam) gives dependency constraints. A source
file can belong to the build while containing aborted attempts or disabled
experiments; neither is an exported theorem.

Build success, admissions, and logical assumptions are separate checks. Some
proofs use classical logic or extensionality. Use `Print Assumptions` on the
theorem of interest rather than inferring its assumptions from imports.

Run `make check` from `Code/` for assumption reports. The separate
[Checks/Assumptions.v](../Code/Checks/Assumptions.v) reports the outcome laws
of `Computation.v`, the arrow law packages, ordered-bind counterexamples, the
separation of the four healthiness classes, and the triples development of
§5, §6 and §9 (morphisms, lifts, both diagrams, examples, rewriting rules,
Dijkstra monads). See the [Checks context](agents/context/Checks.md) for audit
scope and execution details.

The maintained [Code/Makefile](../Code/Makefile) provides this opt-in target;
the audit file is outside `_CoqProject`, so ordinary `make` does not run it.
Each explicit `make check` reruns the reports and returns an error if the
audit file fails to compile. The reports cover selected declarations, not
every theorem in this README, and do not compare assumptions against an allowlist.

Not in the build, deliberately:

- `../Backup/Taxonomy-deprecated/` — earlier iterations. Ignore when grepping for symbol
  references.

The maintained `Code/Makefile` regenerates the gitignored `Makefile.coq` from
`_CoqProject` on every invocation. Verify source removals with a clean build
in an isolated checkout: stale `.vo` files can otherwise satisfy imports of
removed sources. Do not clean a shared workspace while another process is
building it. Editor backups (`.v~`) are outside the build manifest.

## 11. Naming conventions

**Instance names depend on the presentation.** The ExtLib-based developments
in this directory use one underscore for base monads and two for transformer
stacks:

| | pattern | examples |
|---|---|---|
| base monad | `Class_Type` (one underscore) | `Monad_WPure`, `MonadLawsE_WPure`, `Monad_Pred` |
| transformer stack | `Class__Type` (two underscores) | `Monad__WStExc`, `MonadState__WSt` |

The SP monads `ASPMonad.v` / `DSLPMonad.v` / `DSPMonad.v` / `ASLPMonad.v`, and
`Relational/RelMonads.v`, use **one underscore at every layer**: for example, `Monad_ASP`,
`Monad_ASPSt`, `Monad_ASPStExc`, `Eq1_ASPSt`, `MonadLawsE_ASPStExc`, and
`Monad_SPStExc`. The monad-law class used here is `MonadLawsE` (the ITree
class), not `MonadLaws`.

`SP/RawSP.v` names its raw carriers by outcome: `SPPure`,
`SPSt` for plain pairs, `SPStExc` for option outcomes, with the raw orders
`ordSPSt` / `ordSPStExc`. The WP side matches, with `ordWSt` / `ordWStExc`.

## 12. Known duplication

`SP/RawSP.v` keeps raw SP carriers and healthiness predicates of its own,
next to the arrows of `SP/SPostArr.v`, and `WP/WPVariants.v` has a third copy
of the four homomorphism properties for unary WP transformers. `SPostMonad.v`,
the SP monad files, `SPStBindComparisons.v` and `MonotoneSPSt.v` use the raw
ones; nothing in `Verification/` does.
