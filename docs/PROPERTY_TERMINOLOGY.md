# Predicate-transformer healthiness conditions

Research date: 2026-09-10. Subject:
[`PredicateTransformerProperties.v`](../Code/SP/PredicateTransformerProperties.v).

## Adopted name and terminology

**`Code/SP/PredicateTransformerProperties.v`** names the file's role:
it defines predicate-transformer healthiness conditions and proves consequences
and specializations.
The layout places all SP properties under `SP/` and the generic
`ArrowMorphism` material under `Lib/Arrow/`.

The properties follow Back and von Wright's **homomorphism properties of
predicate transformers**, with roots in Dijkstra's weakest-precondition
semantics.[^bw][^dijkstra] Morgan, McIver, and Seidel use the phrase
**“healthiness” (well-formedness) conditions**.[^mms]

Here **healthiness conditions** characterize classes of predicate transformers,
as in refinement calculus and related literature. A transformer is **healthy**
for its class when it satisfies that class's conditions. Different classes may
require different combinations of properties. These terms are not general synonyms
for **well-formed** / **well-formedness**, which we retain for general validity
constraints. Healthiness does not assert algebraic arrow or monad laws.

## SP presentation terminology

**Maillard's SP monad** is the original existential forward predicate-transformer
monad in Maillard et al.'s *Dijkstra Monads for All* (ICFP 2019).[^dm4all]
[`SPostMonad.v`](../Code/SP/SPostMonad.v) represents it as `SPM.SPost`: monotone unary
transformers whose output at precondition `pre` implies `pre`, recorded by
`SPM.Over pre`.

**The demonic variant**, `SPost_dem`, is the universal dual of that construction:
its output at `pre` is implied by `pre`. It uses `ret v pre a := a = v -> pre`
and `bind m k pre b := forall a, k a (m pre a) b`.
[`DSLPMonad.v`](../Code/SP/DSLPMonad.v) defines this carrier as
`SPostDem.SPost`, using the existing `KenjiPureDSLP` restriction. The dual is
introduced in this development; it is not attributed to the original DM4All
artifact. These angelic/demonic names distinguish existential and universal SP
sequencing, rather than classify a computation's nondeterminism.

**Monotone SP arrow** means an ASP or DSLP operation presentation whose carrier
requires only precondition monotonicity. The carrier is `MonotoneSPost`, also
called `MonoPT`, in
[`TransformerRelations.v`](../Code/PTMonadTaxonomy/TransformerRelations.v).
[`SPostArrMonotoneLaws.v`](../Code/Tests/SPostArrMonotoneLaws.v) selects the two
presentations and classifies their laws. The term itself does not assert arrow
laws or preservation of bottom, top, joins, or meets.

**Healthy SP arrow** means an ASP or DSLP arrow in [`SPostArr.v`](../Code/SP/SPostArr.v)
whose carrier bundles its class-defining healthiness conditions:

| Carrier | Conditions besides monotonicity |
|---|---|
| `ASPArr` (also `PureASPostArr`) | strict and disjunctive |
| `DSLPArr` (also `PureDSLPostArr`) | top-preserving and conjunctive |

[`ASPMonad.v`](../Code/SP/ASPMonad.v) identifies Maillard's SP monad with healthy ASP
arrows at input `unit`, and [`DSLPMonad.v`](../Code/SP/DSLPMonad.v) identifies the demonic
variant with healthy DSLP arrows at input `unit`. The maps are inverse up to
pointwise logical equivalence, preserve `ret` and `bind`, and preserve and
reflect the pointwise refinement orders. Thus the restrictions exclude no
healthy values at this input. The angelic results are constructive; the demonic
healthiness, monad laws, and complete equivalence use excluded middle. The
original existential monad need not preserve top, as
`dm4all_not_dslp_healthy` in [`ASPMonad.v`](../Code/SP/ASPMonad.v) shows.

## Exact correspondence with the code

Write `Pred A = A -> Prop`, `⊥ = fun _ => False`, and
`⊤ = fun _ => True`. For `w : Pred A -> Pred B`, equations below mean pointwise
logical equivalence. Back and von Wright §16.1, pp. 259–260 of the accessed draft,
matches the code exactly:[^bw]

| Code property | Exact algebraic condition | Terminology in that text |
|---|---|---|
| `StrictArr w` | `w ⊥ = ⊥` | **strict**, also **nonmiraculous**; preserves bottom |
| `TerminatingArr w` | `w ⊤ = ⊤` | **terminating**, also **nonaborting**; preserves top |
| `ConjunctiveArr w` | `w (⋀ i∈I, pᵢ) = ⋀ i∈I, w pᵢ`, for arbitrary **nonempty** `I` | **conjunctive** |
| `DisjunctiveArr w` | `w (⋁ i∈I, pᵢ) = ⋁ i∈I, w pᵢ`, for arbitrary **nonempty** `I` | **disjunctive** |

The code's `forall b, ~ w ⊥ b` is equivalent to bottom preservation. Its
`inhabited I` premise concerns **the indexing family**, not whether individual
predicates have satisfying states. Families may be infinite. The book's §2.4,
pp. 44–45, calls these **positive meet/join homomorphisms**, reserving **universal
meet/join homomorphisms** for preservation including empty families.[^bw]

### Empty families and the full-preservation lemmas

An empty meet is `⊤`; an empty join is `⊥`. Consequently, in the book's
terminology:[^bw]

- **Universally conjunctive** means preservation of arbitrary meets **including
  the empty meet**. It is equivalent to
  `TerminatingArr w /\ ConjunctiveArr w`.
- **Universally disjunctive** means preservation of arbitrary joins **including
  the empty join**. It is equivalent to
  `StrictArr w /\ DisjunctiveArr w`.

Lemma 2.6(a), p. 45, states these equivalences abstractly. The forward directions
are proved by `terminating_conjunctiveArr_full_meet` and
`strict_disjunctiveArr_full_join`, using `option I` padding. The reverse directions
follow by restricting to inhabited index types and instantiating the unrestricted
law at the empty type. Both nonempty preservation properties imply monotonicity,
as in the code's monotonicity lemmas and Lemma 2.6(b–c).[^bw]

## Dijkstra's conditions

Dijkstra (1975), §3.1, states the **Law of the Excluded Miracle**,
`wp(S, False) = False`, monotonicity, binary conjunction preservation, and binary
disjunction preservation for deterministic statements. For nondeterministic
statements, the last equality becomes an implication.[^dijkstra] Binary
preservation alone does not establish arbitrary nonempty preservation; Back and
von Wright distinguish finite from positive conjunctivity in Exercise 16.4.[^bw]

Dijkstra's `wp(S, True)` is the precondition for guaranteed proper termination
(§§3.1, 3.3). Requiring equality with `True` guarantees termination from **every
initial state**, an additional condition rather than an axiom for every program.
Strictness concerns the impossible postcondition; it is not a termination
guarantee.[^dijkstra]

## Interpretation for forward SP transformers

Back and von Wright §11.2, p. 189, defines transformers that map final-state
predicates to initial-state predicates. Here `(A -> Prop) -> B -> Prop` is used
forward: `A` indexes initial states and `B` indexes results. The same preservation
algebra applies, with an interpretation determined by this orientation.[^bw]

For a relation `R : A -> B -> Prop` (the existing `Rel A B` carrier),
[`RelSPostArr.v`](../Code/Relational/RelSPostArr.v) computes two readings. Neither reading adds a
carrier or stores a transformer:

```text
asp  R P b = exists a, P a /\ R a b
dslp R P b = forall a, R a b -> P a

asp  R ⊥ b <-> False
asp  R ⊤ b <-> exists a, R a b
dslp R ⊤ b <-> True
```

Thus `TerminatingArr (asp R)` means **every output has some predecessor**. For a
total function `bool -> bool` that always returns `false`, its relational `asp`
fails this property at `true`. Conversely, `dslp R` preserves top for the empty relation, which can
record the terminating runs of an everywhere-diverging program. In SP prose,
`TerminatingArr` means **top preservation**, called “terminating” in the
refinement-calculus terminology, rather than a runtime termination guarantee.

Hino et al. characterize existential and universal backward transformers
`wp◇(R)` and `wp□(R)` by full join and meet preservation (Theorems 1.1 and 2.5).
Applied to `Rᵒᵖ b a := R a b`, their formulas give this project's `asp R` and
`dslp R`, respectively. This connects the forward use to the same algebra.[^hino]

## Sources and verification limits

The primary texts below were inspected directly. **Book pages refer to printed
labels in the December 31, 1997 draft**; pagination in the published 1998 edition
was not verified. Dijkstra was read in the university archive's transcription;
Hino et al.'s theorem numbers refer to the cited arXiv version.

[^dm4all]: Kenji Maillard, Danel Ahman, Robert Atkey, Guido Martínez, Cătălin
    Hriţcu, Exequiel Rivas, and Éric Tanter, [*Dijkstra Monads for
    All*](https://doi.org/10.1145/3341708), *Proceedings of the ACM on Programming
    Languages* 3 (ICFP), Article 104, 2019, §4.1, p. 104:13. The original
    artifact's `Module StrongestPostcondition` defines `SP` and
    `ForwardPredTransformer` in
    [`theories/sprop/SpecificationMonads.v`](https://gitlab.inria.fr/kmaillar/dijkstra-monads-for-all/-/blob/ce2fa9311a8dc1df83014bd39c369a6a7ee7e190/theories/sprop/SpecificationMonads.v#L476-555).

[^bw]: Ralph-Johan Back and Joakim von Wright, *Refinement Calculus: A Systematic
    Introduction*. [Complete draft, December 31, 1997, hosted by
    EPFL](https://lara.epfl.ch/w/_media/sav08:backwright98refinementcalculus.pdf).
    §2.4, pp. 44–46, Lemma 2.6; §11.2, pp. 189–191; §16.1, pp. 259–261;
    Exercise 16.4, p. 267.
    [Published book DOI](https://doi.org/10.1007/978-1-4612-1674-2).

[^dijkstra]: Edsger W. Dijkstra, “Guarded commands, non-determinacy and formal
    derivation of programs,” *Communications of the ACM* 18(8), 1975,
    pp. 453–457. [EWD472, University of Texas archive
    transcription](https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD472.html),
    §3.1, numbered properties 1–4 and final note; §3.3, discussion before
    Theorem 4. [Manuscript scan](https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF).

[^mms]: Carroll Morgan, Annabelle McIver, and Karen Seidel, “Probabilistic
    Predicate Transformers,” *ACM Transactions on Programming Languages and
    Systems* 18(3), 1996, pp. 325–353. [Author-hosted
    PDF](https://cgi.cse.unsw.edu.au/~carrollm/probs/Papers/Morgan-96d.pdf).
    §1, p. 327, supplies the quoted terminology. §6.1, pp. 337–338, explicitly
    relies on finite state spaces when using a finite-conjunction formulation.

[^hino]: Wataru Hino, Hiroki Kobayashi, Ichiro Hasuo, and Bart Jacobs,
    “Healthiness from Duality,” [arXiv:1605.00381v1, May 2,
    2016](https://arxiv.org/abs/1605.00381v1);
    [HTML text](https://arxiv.org/html/1605.00381v1).
    §1, Theorem 1.1, equation (1), and “Preliminaries and Notations”;
    §§2.1–2.2, Theorem 2.5. Preservation includes empty families.
