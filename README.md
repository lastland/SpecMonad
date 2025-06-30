This is a work-in-progress Coq development exploring the connection between
incorrectness logic and the Dijkstra monad/specification monads.

The repo contains a number of files---some of them are work in progress or
outdated. You can find all the most updated Coq files in
[_CoqProject](Code/_CoqProject).

# Dependencies

- coq-ext-lib
- coq-hammer

Version info can be found in [this opam file](Code/coq-spec-monad.opam).

# The current status

There is currently a formalization of applying incorrectness logic to one type
of specification monad, i.e., the forward predicate transformer. Then we can use
the classical Dijkstra monad framework to related incorrectness reasoning with
effect observations. This allows us to reason about "incorrectness" (either for
bug finding or for reasoning about existence of a branch in demonic
nondeterminism) based on specification monad, instead on effect observation over
any actual computation monads.

## Question

- What is a good application of this?

## Current issues 

- We use the forward predicate transformer, which makes reasoning (especially
  automated reasoning) hard. This is because there are `exists`s in every
  monadic bind in the specification monad of the forward predicate transformer.
  
- There is no compositional reasoning rule for incorrectness logic at this
  point.
  
- There is no proof about laws regarding interactions between incorrectness
  logic and Hoare logic at this point.

- No proofs for monad laws (but they have been proven in DM4Free paper).

## Potential future directions

- *Backward reasoning*: Look into works like [underspecified incorrectness
  logic](https://doi.org/10.1145/3704850).
  
- What about other predicate transformers?

- What about [outcome logic](https://doi.org/10.1145/3586045)?

- Nondeterminism and non-termination.

- Compositional reasoning with incorrectness logic.

- Property-based "testing", but based on automated theorem provers and
  specification monad? It would be challenging now though with all the
  existentials.
