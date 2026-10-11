# SpecMonad

SpecMonad is a work-in-progress Coq development studying how specification
monads support correctness and incorrectness reasoning about programs.

The development in [`Code/`](Code/README.md) is organized by the sections of
the paper; [PAPER.md](PAPER.md) maps each claim to its Rocq name. The
[design notes](docs/design.md) explain the semantics, representations, and
naming conventions. Use the [context map](docs/agents/context/README.md) to navigate the rest
of the repository. The [build manifest](Code/_CoqProject) lists the normal
build's sources; other files include historical and unfinished experiments.

## Dependencies

The packages and their version constraints are listed in the
[opam manifest](Code/coq-spec-monad.opam).

## Build

    cd Code
    make

The committed `Code/Makefile` regenerates the gitignored `Makefile.coq`
from `_CoqProject` on every invocation, so no manual generation step is
needed. Build membership
does not by itself certify every statement: the one unfinished proof and the
paper claims that are not formalized are listed in
[PAPER.md](PAPER.md#gaps-and-differences-from-the-paper).

Run `make check` from `Code/` for the opt-in reports of selected theorem
assumptions. This target is separate from the normal build and does not check
assumptions against an allowlist. See the
[build and audit details](docs/design.md#10-build-status).

## The current status

The specification carriers are independent of concrete computation
monads. **Monad morphisms connect computations to specifications**, choosing
how to interpret their outcomes.

What is formalised:

- **One base computation monad and its transformer stacks**: non-empty
  nondeterminism with divergence (`divndNE`), under `stateT S` and under
  `stateT S` over `optionT` for exceptions.

- **Four strongest-postcondition (SP) specification monads** — angelic (ASP),
  demonic liberal (DSLP), demonic (DSP), and angelic liberal (ASLP). The public
  monads fix the input of canonical healthy arrows and reuse the generic
  arrow-derived return, bind, and monad laws. Pure, state, and state/option
  stacks are provided.

- **Canonical property-only SP arrows**, with shared relational law proofs.
  `PureASPostArr` / `PureDSLPostArr` are compatibility aliases for the public
  `ASPArr` / `DSLPArr`; their operations and dictionaries are shared. ASP/DSLP
  have lawful option/state stacks,
  full application coherence, and operation-preserving equivalences to the
  existing `Rel` carrier under the selected pointwise equalities.
  [`RelSPostArr.v`](Code/Relational/RelSPostArr.v)
  computes the two readings of a relation, reusing `Rel`'s laws and stacks. See
  [`SPostArr.v`](Code/SP/SPostArr.v) and the checked
  [examples](Code/Tests/SPostArrExamples.v).

- **Weakest-precondition (WP) specifications**, `WPure` and its state and
  state/option stacks. `WPure` bundles postcondition monotonicity, which the
  adjunction and congruence proofs use. The binary `WPArr` instead uses the raw
  `WPureT` carrier.

- **Five base specification monads**, from Maillard et al.'s
  [*Dijkstra Monads for All*](https://doi.org/10.1145/3341708) (ICFP 2019),
  presented as unary monads with five adjunctions in
  `BaseGaloisConnections.v`. Their laws use pointwise logical equivalence
  rather than equality of bundled values.

- **Monad morphisms and one general triple.** Eight readings (four WP, four
  SP) are defined once at the base as monad morphisms and lifted through the
  monad and arrow transformers to state and to state with exceptions.
  `triple θ m k P Q` is defined for any monad morphism `θ`; its sixteen
  instances are the correctness and incorrectness triples, and the triple of
  a lifted morphism is the base triple re-indexed. See
  [`Verification/Base/MorphismsPure.v`](Code/Verification/Base/MorphismsPure.v).

- **The taxonomy of triples**: the 26 edges of Verscht and Kaminski's diagram
  (implications, contrapositives, and the two Galois connections between WP
  and SP), with state and with state and exceptions, in
  [`Verification/State/TripleTaxonomySt.v`](Code/Verification/State/TripleTaxonomySt.v). A separate
  development relates the specification monads themselves
  (`PTMonadTaxonomy/MonadTaxonomy.v`).

- **Examples**: one verified program for each of the sixteen triple kinds,
  and a withdrawal example contrasting angelic WP coverage of every input
  with ASP reachability from some input.

- **Incorrectness principles** from Peter W. O'Hearn's
  [*Incorrectness Logic*](https://doi.org/10.1145/3371078) (POPL 2020), proved
  over the ASP triples, with demonic liberal WP variants, in
  [`Verification/State/InCorrectnessPrinciples.v`](Code/Verification/State/InCorrectnessPrinciples.v).

- **Dijkstra monads**: the Dijkstra monad of any monad morphism into an
  ordered monad, at every lifted morphism, with triples identified with
  typings where that is exact. See the
  [Dijkstra context](docs/agents/context/Verification.md).

## Question

- What is a good application of this?

## Current issues

- Existential witnesses in forward sequencing make some proofs, especially
  automated proofs, difficult. This is not a property of every specification
  bind: DSLP also has a universal formulation.

- Stateful DSP and ASLP sequencing recovers and composes relations before
  reading them again. DSP probes at top and a co-singleton (all states except
  one); ASLP probes at bottom and a singleton. With state their binds do not
  preserve the pointwise orders, despite satisfying the monad laws, and no
  other bind does. See `not_OrderedMonad_DSPSt` and
  `dsp_arbitrary_bind_impossible` in
  [DSPMonad.v](Code/SP/DSPMonad.v), and their duals in
  [ASLPMonad.v](Code/SP/ASLPMonad.v).

- ASP under-approximation with the chosen **in-monad target** uses an order at
  one precondition and requires that precondition to be inhabited. Comparisons
  against raw transformers have a different contract; they must not be confused
  with these in-monad characterizations.

- The option-outcome and terminating-slice developments repeat much of their
  structure. Sharing that structure remains a possible refactor, not an
  implemented abstraction.

## Potential future directions

- *Backward reasoning*: Explore Verbeek et al.'s
  [*On Extending Incorrectness Logic with Backwards Reasoning*](https://doi.org/10.1145/3704850)
  (POPL 2025).

- What about other predicate transformers?

- What about Zilberstein, Dreyer, and Silva's
  [*Outcome Logic: A Unifying Foundation for Correctness and Incorrectness Reasoning*](https://doi.org/10.1145/3586045)
  (PLDI 2023)?

- Compositional reasoning with incorrectness logic, beyond the O'Hearn
  principles already proved.

- Explore theorem-prover-based testing with specification monads, including
  how to automate the existential witnesses these specifications require.
