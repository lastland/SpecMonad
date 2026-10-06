# SpecMonad

SpecMonad is a work-in-progress Coq development studying how specification
monads support correctness and incorrectness reasoning about programs.

The core development is [`Code/Taxonomy/`](Code/Taxonomy). Its
[README](Code/Taxonomy/README.md) explains the semantics, representations, and
naming conventions. Use the [context map](CONTEXT-MAP.md) to navigate the rest
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
does not certify that every exploratory statement in a file has been proved:
some attempts end with `Abort` or remain commented out.

Run `make check` from `Code/` for the opt-in reports of selected theorem
assumptions. This target is separate from the normal build and does not check
assumptions against an allowlist. See the
[build and audit details](Code/Taxonomy/README.md#11-build-status).

## The current status

The Taxonomy specification carriers are independent of concrete computation
monads. **Observations connect computations to specifications**, choosing how
to interpret their outcomes. In particular, an option outcome can represent
an exception or divergence; the observation determines which.

What is formalised:

- **Four stateful computation models**, combining exceptions, nondeterminism,
  and divergence, plus the state-free `divnd` and reader-indexed `rddivnd`.

- **Four strongest-postcondition (SP) specification monads** — angelic (ASP),
  demonic liberal (DSLP), demonic (DSP), and angelic liberal (ASLP). Their
  well-formedness conditions restrict the raw transformer type
  `(S -> Prop) -> Outcome -> Prop` to support lawful sequencing.
  Each comes with `Monad`, `Eq1`, and
  `MonadLawsE`, in both option-outcome and terminating-slice indexings.
  Pure and reader-indexed variants are also defined.

- **Property-only ASP and DSLP arrows**, with lawful option/state stacks,
  full application coherence, and operation-preserving equivalences to the
  existing `Rel` carrier under the selected pointwise equalities.
  [`RelSPostArr.v`](Code/Taxonomy/Arrows/RelSPostArr.v)
  computes the two readings of a relation, reusing `Rel`'s laws and stacks. See
  [`SPostArr.v`](Code/Taxonomy/Arrows/SPostArr.v) and the checked
  [examples](Code/Taxonomy/Arrows/Examples/SPostArrExamples.v).

- **Weakest-precondition (WP) specifications**, `WPure` and its `stateT`/`optionT`
  stacks. `WPure` bundles postcondition monotonicity, which the adjunction and
  congruence proofs use. The binary `WPArr` instead uses the raw `WPureT` carrier.

- **The five base specification monads of *Dijkstra Monads For All*** (ICFP
  2019), presented as unary monads with five adjunctions in
  `BaseGaloisConnections.v`. Their laws use pointwise logical equivalence
  rather than equality of bundled values.

- **Effect observations and triples**, with return/bind preservation proved for
  the base SP observations, arrow-derived ASP/DSLP observations, and the WP
  observations of `stdivexcnd` and `stdivndNE`. The other WP modules provide
  readings and examples, but do not prove local return/bind preservation laws.

- **The taxonomy**: how the observations relate to one another — inclusions,
  contrapositive dualities, and the implications between the triples built on
  them. The WP/SP comparison theorems identify specific triple directions over
  the same terminating relation. The withdrawal example separately contrasts
  angelic WP coverage of every input with ASP reachability from some input.

- **O'Hearn's incorrectness principles** over the ASP triples, in
  [`InCorrectnessPrinciples.v`](Code/Taxonomy/InCorrectnessPrinciples.v).

## Question

- What is a good application of this?

## Current issues

- Existential witnesses in forward sequencing make some proofs, especially
  automated proofs, difficult. This is not a property of every specification
  bind: DSLP also has a universal formulation.

- Stateful DSP and ASLP sequencing recovers and composes relations before
  reading them again. DSP probes at top and a co-singleton (all states except
  one); ASLP probes at bottom and a singleton. Their state-only binds do not
  preserve the chosen global pointwise orders, despite satisfying the monad laws. See
  [the ordered-bind counterexamples](Code/Taxonomy/BaseSpecMonads/SPBindOrderCounterexample.v).

- ASP under-approximation with the chosen **in-monad target** uses an order at
  one precondition and requires that precondition to be inhabited. Comparisons
  against raw transformers have a different contract; they must not be confused
  with these in-monad characterizations.

- The option-outcome and terminating-slice developments repeat much of their
  structure. Sharing that structure remains a possible refactor, not an
  implemented abstraction.

## Potential future directions

- *Backward reasoning*: Look into works like [underspecified incorrectness
  logic](https://doi.org/10.1145/3704850).

- What about other predicate transformers?

- What about [outcome logic](https://doi.org/10.1145/3586045)?

- Compositional reasoning with incorrectness logic, beyond the O'Hearn
  principles already proved.

- Explore theorem-prover-based testing with specification monads, including
  how to automate the existential witnesses these specifications require.
