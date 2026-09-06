# State, exceptions, nondeterminism, and divergence

This directory instantiates the generic Dijkstra-monad recipes for a
computational monad with:

- mutable state;
- exceptions;
- nondeterministic choice; and
- divergence.

It contains one computational monad, several specification monads, eight
observations, and sixteen program logics. The sixteen logics are the eight
observation families used in the two approximation directions, `Over` and
`Under`.

## Computational monad

[`Program.v`](Program.v) defines

```coq
nditprog S A := stateT S (optionT (optionT SetM)) A
```

where `SetM A := A -> Prop` represents nondeterministic sets of outcomes.
Running a computation from a state therefore produces a predicate over

```text
option (option (A * S))
```

with the following interpretation:

| Raw outcome | Meaning |
|---|---|
| `Some (Some (a, s'))` | normal termination with value `a` and final state `s'` |
| `Some None` | exceptional termination |
| `None` | divergence |

The main operations are `nditRet`, `nditBind`, `nditGet`, `nditPut`,
`nditRaise`, `nditCatch`, `nditOr`, and `nditSpin`. The lemma
`outcomes_bind` gives the operational decomposition of a bind and is reused
by all WP observations.

## Specification monads

| File | Carrier | Role and order |
|---|---|---|
| [`WP.v`](WP.v) | `PureWP A := (A -> Prop) -> Prop` | Pure predicate transformers. |
| [`WP.v`](WP.v) | `BaseProgWP S := stateT S (optionT PureWP)` | Stateful predicate transformers whose postconditions range over normal and exceptional results. |
| [`WP.v`](WP.v) | `ProgWP S A` | `BaseProgWP` restricted to monotone predicate transformers. Its refinement order `wpLe` is reverse implication. |
| [`SP.v`](SP.v) | `ProgSP S A := (S -> Prop) -> option (A * S) -> Prop` | The ambient SP predicate-transformer space, shared by all four SP monads. Not a monad; `ordProgSP` is inclusion. |
| [`Logics/ASP.v`](Logics/ASP.v) | `ASPProgSP S A := { w : ProgSP S A \| SingletonProg w }` | Angelic (join-preserving) SP. Order `aspLe`. |
| [`Logics/DLSP.v`](Logics/DLSP.v) | `DSLPProgSP S A := { w \| MSingletonProg w }` | Demonic liberal (meet-preserving) SP. Order `dslpLe`. |
| [`Logics/DSP.v`](Logics/DSP.v) | `DSPProgSP S A := { w \| StrictPositivelyMeetPreservingProg w }` | Demonic SP: angelic *and* demonic-liberal. Order `dspLe`. |
| [`Logics/ALSP.v`](Logics/ALSP.v) | `ASLPProgSP S A := { w \| TerminatingPositivelyJoinPreserving w }` | Angelic liberal SP: angelic *or* demonic-liberal. Order `aslpLe`. |
| [`PrePost.v`](PrePost.v) | `PP S A := (S -> Prop) * (S -> option (A * S) -> Prop)` | Hoare-style pre/post specifications. `ppLe` is contravariant in the precondition and covariant in the postcondition. |

Each SP logic module owns its healthy carrier, monad laws, ordered-monad
structure, truth bounds, logical meet/join, generic `LogicRecipe` constructor,
concrete observation, and worked logic.

### SP organization

`SP.v` owns only the common foundation: the ambient carrier `ProgSP`, the
four healthiness conditions
  (`StrictProg`, `TerminatingProg`, `ConjunctiveProg`, `DisjunctiveProg`),
the ambient order `ordProgSP` with `pp2_over` / `pp2_under`, and the shared
relation infrastructure (`SPRel`, `relLe`, `retRel`, `compRel`, `obsRel`).

The SP logic modules then form the dependency chain
`Logics/ASP.v` → `Logics/DLSP.v` → `Logics/DSP.v` → `Logics/ALSP.v`.
Each module owns the corresponding healthy subtype and all of its
specification-monad and observation infrastructure.

The definitions are a local copy of the healthy SP monads of
`SPSpecMonads.v`, the option-outcome variant used by
`SPNonDetItObservations.v` at commit `1c6e8d21`. The sibling
`SPSimplerSpecMonads.v` is for plain outcomes without exceptions; this recipe
needs the finite outcome type `option (A * S)`. They are copied rather than
imported because `Recipes` must have no direct or transitive dependency on
`Taxonomy`.

## Observations

Write

```text
Raw_m(s, oa) := oa is a raw outcome of running m from s
R_m(s, r)    := obsRel m s r
```

where `r : option (A * S)` is a *finite* outcome: `Some (a, s')` is normal
termination and `None` is an exception. `obsRel` deliberately omits the raw
divergence outcome.

### Weakest-precondition observations

For a postcondition `Q : option (A * S) -> Prop`, the four observations into
`ProgWP` are:

| Observation | Definition at initial state `s` | Interpretation |
|---|---|---|
| `awpObs` / `obsAWP` | `exists r, Raw_m(s, Some r) /\ Q r` | Some finite outcome satisfies `Q`; divergence is not a witness. |
| `dwpObs` / `obsDWP` | Every raw outcome is finite and every finite outcome satisfies `Q`. | All branches terminate finitely and satisfy `Q`. |
| `alwpObs` / `obsALWP` | `(exists r, Raw_m(s, Some r) /\ Q r) \/ Raw_m(s, None)` | Some finite outcome satisfies `Q`, or a divergent branch exists. |
| `dlwpObs` / `obsDLWP` | Every finite outcome satisfies `Q`; divergent outcomes are accepted. | All terminating branches satisfy `Q`; divergence is allowed. |

Exceptions are finite outcomes in all four observations, so whether an
exception is accepted is determined by `Q None`.

### Strongest-postcondition observations

For a precondition `P : S -> Prop` and finite result
`r : option (A * S)`, define

```text
E(P, r) := exists s, P s /\ R_m(s, r)
U(P, r) := forall s, R_m(s, r) -> P s
```

The four SP observations differ only in how these two readings are combined,
and each lands in the healthy monad that its combination inhabits:

| Observation | Specification carrier | Transformer |
|---|---|---|
| `obsASP` | `ASPProgSP` | `E(P, r)` |
| `obsDSLP` | `DSLPProgSP` | `U(P, r)` |
| `obsDSP` | `DSPProgSP` | `E(P, r) /\ U(P, r)` |
| `obsASLP` | `ASLPProgSP` | `E(P, r) \/ U(P, r)` |

These are exactly the observation formulas of Taxonomy's
`SPNonDetItObservations.v`. Each one is defined in its own logic module —
`obsASP` in `Logics/ASP.v`, `obsDSLP` in `Logics/DLSP.v`, `obsDSP` in
`Logics/DSP.v`, `obsASLP` in `Logics/ALSP.v` — together with its `ret`/`bind`
preservation proofs, its monad-morphism instance and its `LogicRecipe`
(`aspRecipe`, `dslpRecipe`, `dspRecipe`, `aslpRecipe`), obtained from the
generic constructor of the corresponding SP layer. Only the shared relation
`obsRel` lives in `SP.v`.

Because `obsDSP` and `obsASLP` are literally the conjunction and the
disjunction of `obsASP` and `obsDSLP`, `Logics/DSP.v` and `Logics/ALSP.v`
import `Logics/ASP.v` and `Logics/DLSP.v`; `Logics/DLSP.v` imports
`Logics/ASP.v` for the contrapositive theorem.

Because each of the four readings is a bijection with the observed relation
`R_m` — inverted by `aspRel` / `dslpRel` / `dspRel` / `aslpRel`, with
`aspOf` / `dslpOf` / `dspOf` / `aslpOf` going the other way — every one of
the four monads is ordered by inclusion of the observed relation. On
`ASPProgSP` this is exactly the transformer inclusion `ordProgASP`
(`asp_le_transformer`); on `DSLPProgSP` it is `ordProgDSLP` reversed
(`dslp_le_transformer`), since reading a relation as a DSLP is antitone. On
all four it is a complete lattice: bottom is the empty relation, top the
full one, meet is intersection, join is union, and `bind` is monotone
because it is relational composition (`compRel`).

`obsASP` and `obsDSLP` are contrapositives of each other, and so are
`obsDSP` and `obsASLP` (`obsASP_contrapositive`, `obsDSP_contrapositive`).

## The sixteen logics

For every observation family, the code exposes both approximation directions.
Thus the eight rows below index all sixteen logics.

| Family | File | `Over` logic | `Under` logic |
|---|---|---|---|
| AWP | [`Logics/AWP.v`](Logics/AWP.v) | `AWPTriple Over m P Q` | `AWPTriple Under m P Q` |
| DWP | [`Logics/DWP.v`](Logics/DWP.v) | `DWPTriple Over m P Q` | `DWPTriple Under m P Q` |
| ALWP | [`Logics/ALWP.v`](Logics/ALWP.v) | `ALWPTriple Over m P Q` | `ALWPTriple Under m P Q` |
| DLWP | [`Logics/DLWP.v`](Logics/DLWP.v) | `DLWPTriple Over m P Q` | `DLWPTriple Under m P Q` |
| ASP | [`Logics/ASP.v`](Logics/ASP.v) | `ASPTriple Over m P Q` | `ASPTriple Under m P Q` |
| DLSP | [`Logics/DLSP.v`](Logics/DLSP.v) | `DLSPTriple Over m P Q` | `DLSPTriple Under m P Q` |
| DSP | [`Logics/DSP.v`](Logics/DSP.v) | `DSPTriple Over m P Q` | `DSPTriple Under m P Q` |
| ALSP | [`Logics/ALSP.v`](Logics/ALSP.v) | `ALSPTriple Over m P Q` | `ALSPTriple Under m P Q` |

[`Logics/Taxonomy.v`](Logics/Taxonomy.v) relates the sixteen logics. It
formalizes the direct implication arrows (with `Feasible m` where a
universal observation must produce an existential witness), the
contrapositive equivalences, and the WP/SP Galois equivalences.

For the unary pre/post specifications used by these triples, the directions
expand as follows.

For a WP observation `W_m`:

```text
Over:  forall s, P s -> W_m s Q
Under: forall s, W_m s Q -> P s
```

For an SP observation `w = getProg* (obs* m)`:

```text
Over:  forall r, w P r -> Q r
Under: forall r, Q r -> w P r
```

`Over` over-approximates the observation and `Under` under-approximates it.
This directional choice is independent of the angelic/demonic and
total/liberal choices made by an observation.

## Connections between specification monads

[`PrePost.v`](PrePost.v) proves the pre/post ↔ weakest-precondition Galois
connection and the raw characterisations of both SP triple directions. `⊑`
denotes the refinement order of the carrier on the corresponding side.

### Pre/post specifications and weakest preconditions

```text
pp2wp pq ⊑ w    <->    pq ⊑ wp2pp w
```

Consequently, `pp2wp` is left adjoint to `wp2pp`:

```text
PP  -- pp2wp -->  ProgWP
PP  <-- wp2pp --  ProgWP
        pp2wp ⊣ wp2pp
```

- `pp2wp (P, R)` requires `P s` and requires every `R`-related result to
  satisfy the supplied postcondition.
- `wp2pp w` extracts the precondition `w True` and relates an outcome `r`
  when every postcondition accepted by `w` contains `r`.
- The generic theorem is `pp_wp_galois`.
- Its observation-specific instances are `awp_pp_galois`,
  `dwp_pp_galois`, `alwp_pp_galois`, and `dlwp_pp_galois`.

### Strongest postconditions and pre/post specifications

An SP specification is a *predicate transformer*, so the legacy
"full-pre / forget-pre" adjunction `sp2pp ⊣ pp2sp` — which only made sense
while `ProgSP S A` was the relation `S -> option (A * S) -> Prop`, whose data
is literally the postcondition field of `PP` — is neither typeable nor
meaningful any more. It has been removed rather than kept as a misleading
wrapper.

Its role is taken by the two *raw comparison targets* of `SP.v`, which
turn a unary pre/post pair into a plain (unhealthy) `ProgSP`:

```coq
pp2_over  pre post := fun p r => (forall s, p s -> pre s) -> post r
pp2_under pre post := fun p r => (forall s, pre s -> p s) /\ post r
```

Both triple directions are then inclusions in the ambient order
`ordProgSP`, for any observation that is monotone in its precondition:

```text
Over:   (forall r, w pre r -> post r)   <->   ordProgSP w (pp2_over pre post)
Under:  (forall r, post r -> w pre r)   <->   ordProgSP (pp2_under pre post) w
```

- The generic theorems are `sp_over_raw` and `sp_under_raw`, whose only
  hypothesis is `MonoSP w`.
- The four monotonicity witnesses are `aspMonoSP`, `dslpMonoSP`,
  `dspMonoSP`, and `aslpMonoSP`.
- Their observation-specific instances are `asp_triple_raw`,
  `dlsp_triple_raw`, `dsp_triple_raw`, and `alsp_triple_raw`.

Neither target is healthy — at the empty precondition `pp2_over` still
yields `post r`, and at the full one `pp2_under` holds with no single state
carrying `pre` — which is why the comparison happens in the ambient
`ProgSP` and not inside a monad. Two directions do have in-monad targets:
`asp_over_inmonad` compares in `ordProgASP`, and `dlsp_under_inmonad`
compares in `ordProgDSLP` (with the inclusion reversed).

Putting the connections together:

```text
                                          pp2wp ⊣ wp2pp
ASPProgSP  \
DSLPProgSP  \  getProg*
DSPProgSP   -----------> ProgSP  <-- pp2_over / pp2_under --  PP  <===>  ProgWP
ASLPProgSP  /                (ordProgSP)
```

## File index

| File | Contents |
|---|---|
| [`Program.v`](Program.v) | Computational monad, effects, transformer laws, and `outcomes_bind`. |
| [`WP.v`](WP.v) | WP carriers, orders, laws, lattice operations, and recipe. |
| [`SP.v`](SP.v) | Ambient `ProgSP`, the four healthiness conditions, `ordProgSP` with `pp2_over` / `pp2_under`, and the shared relation layer (`SPRel`, `retRel`, `compRel`, `obsRel`). |
| [`PrePost.v`](PrePost.v) | Pre/post monad, approximation interpretations, the PP/WP Galois connection, and the raw SP triple characterisations. |
| [`Examples.v`](Examples.v) | Shared example programs and predicates. |
| [`Logics/ASP.v`](Logics/ASP.v) | The angelic SP monad, order, recipe, observation, and logic. |
| [`Logics/DLSP.v`](Logics/DLSP.v) | The demonic-liberal SP monad, order, recipe, observation, and logic. |
| [`Logics/DSP.v`](Logics/DSP.v) | The demonic SP monad, order, recipe, observation, and logic. |
| [`Logics/ALSP.v`](Logics/ALSP.v) | The angelic-liberal SP monad, order, recipe, observation, and logic. |
| [`Logics/Taxonomy.v`](Logics/Taxonomy.v) | Implications, contrapositive equivalences, and Galois equivalences relating the sixteen logics. |
| [`Logics/`](Logics/) | The four WP logic modules and four self-contained SP logic modules. |
