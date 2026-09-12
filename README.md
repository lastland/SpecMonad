This is a work-in-progress Coq development exploring the connection between
incorrectness logic and the Dijkstra monad/specification monads.

The repo contains a number of files---some of them are work in progress or
outdated. You can find all the most updated Coq files in
[_CoqProject](Code/_CoqProject).

The core of the development is [`Code/Taxonomy/`](Code/Taxonomy); its
[README](Code/Taxonomy/README.md) is the detailed map of the design, the file
layout and the naming conventions.

# Dependencies

The packages and their version constraints are listed in the
[opam manifest](Code/coq-spec-monad.opam).

# Build

    cd Code
    coq_makefile -f _CoqProject -o Makefile
    make

`Makefile` is gitignored, so it has to be regenerated. The files listed in
`_CoqProject` build clean, with no `Admitted`.

# The current status

The development is organised around one separation: **the specification side
never mentions a computation monad**, only the *outcome type*. Everything that
depends on a particular computation monad is confined to an observation file.

What is formalised:

- **Four computation monads** over `stateT`/`optionT`, covering state,
  exceptions, nondeterminism and divergence in the four useful combinations.

- **Four strongest-postcondition specification monads** — angelic SP, demonic
  liberal SP, demonic SP, angelic liberal SP — each carved out of the raw
  transformer type `(S -> Prop) -> Outcome -> Prop` by a well-formedness condition,
  because the raw type is *not* a monad. Each comes with `Monad`, `Eq1` and all
  four monad laws, in both the exception-outcome and terminating-slice
  indexings.

- **Property-only ASP and DSLP arrows**, with lawful option/state stacks,
  full application coherence, and operation-preserving equivalence to the
  coupled relation/transformer presentation. See
  [`SPostArr.v`](Code/Taxonomy/Arrows/SPostArr.v) and the checked
  [examples](Code/Taxonomy/Arrows/Examples/SPostArrExamples.v).

- **The weakest-precondition side**, `WPure` and its `stateT`/`optionT` stacks,
  with the carrier restricted to *monotone* transformers — `monotonicity_is_needed`
  shows the `PrePost -| WPure` adjunctions are false without that restriction.

- **The five base specification monads of *Dijkstra Monads For All*** (ICFP
  2019) ported as unary monads with all five adjunctions between them, and every
  proof axiom-free.

- **Effect observations** from each computation monad into the SP and WP
  specification monads, each proved to be a **monad morphism**, together with
  the triples they support and the refinement (order-theoretic) form of each
  triple.

- **The taxonomy**: how the observations relate to one another — inclusions,
  contrapositive dualities, and the implications between the triples built on
  them. `Section GaloisConnection` identifies the angelic-WP and demonic-liberal-WP
  triples with the SP ones, so the same program and postcondition can be read as
  either a Hoare-style or an O'Hearn-style statement.

- **O'Hearn's incorrectness principles** over the ASP triples, in
  [`InCorrectnessPrinciples.v`](Code/Taxonomy/InCorrectnessPrinciples.v).

## Question

- What is a good application of this?

## Current issues

- The forward predicate transformer makes reasoning (especially automated
  reasoning) hard: there is an `exists` in every monadic bind.

- Demonic SP and angelic liberal SP are neither monotone nor antitone in the
  underlying relation, so their `bind` cannot be a forward pass — it has to
  *recover* the relation by probing at two constant preconditions. That is most
  of the bulk of `DSPMonad.v` and `ASLPMonad.v`.

- The under-approximate (incorrectness) triple is not an instance of the global
  refinement order; it only works in the order **scoped to a single
  precondition**. The two directions therefore need two different orders.

- The exception-outcome and terminating-slice developments are near-copies of
  one another. Parameterising over an abstract outcome functor would collapse
  them.

## Potential future directions

- *Backward reasoning*: Look into works like [underspecified incorrectness
  logic](https://doi.org/10.1145/3704850).

- What about other predicate transformers?

- What about [outcome logic](https://doi.org/10.1145/3586045)?

- Compositional reasoning with incorrectness logic, beyond the O'Hearn
  principles already proved.

- Property-based "testing", but based on automated theorem provers and
  specification monad? It would be challenging now though with all the
  existentials.
