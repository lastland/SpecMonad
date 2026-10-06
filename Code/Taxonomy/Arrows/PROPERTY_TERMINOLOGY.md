# Predicate-transformer well-formedness

Research date: 2026-09-10. Subject:
[`PredicateTransformerProperties.v`](PredicateTransformerProperties.v).

## Adopted name and terminology

**`Code/Taxonomy/Arrows/PredicateTransformerProperties.v`** names the file's role:
it defines well-formedness properties and proves consequences and specializations.
The agreed layout places all SP properties under `Taxonomy/Arrows/` and the
generic `ArrowMorphism` material under `Classes/`.

The properties follow Back and von Wright's **homomorphism properties of
predicate transformers**, with roots in Dijkstra's weakest-precondition
semantics.[^bw][^dijkstra] The project uses **well-formed** and **well-formedness**.
Morgan, McIver, and Seidel use the phrase **“healthiness” (well-formedness)
conditions**.[^mms] Different combinations select different well-formed fragments.

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
[`RelSPostArr.v`](RelSPostArr.v) computes two readings. Neither reading adds a
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
