# STEx

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

STEx gives forward specifications for state computations with exceptions.
[Examples.v](Examples.v) defines computations in ExtLib's `stateT S (sum E)`;
[STEx.v](STEx.v) defines the specification carrier, its observation, and
verification rules connecting specifications to those computations.

## Established vocabulary and contracts

- `STEx S E A` maps an initial state and `pre : Prop` to propositions over
  `E + A * S`, each bundled with a proof that it implies `pre`.
  `inl e` is an exception; `inr (a, s)` is a normal result and final state.
  The carrier does not bundle monotonicity in `pre`.
- `retSTEx`, `bindSTEx`, `getSTEx`, `putSTEx`, `raiseSTEx`, and `catchSTEx`
  supply `Monad__STEx`, `MonadState__STEx`, and `MonadExc__STEx`.
  Bind continues from normal results and propagates exceptions.
- Exceptions contain no final state. `catchSTEx m c` runs `c e` at the
  original state `s0`, with the proposition in `m s0 pre (inl e)` as its
  precondition. The file explicitly leaves monad laws unproved.
- `obsSTEx m s0 pre r` asserts `runStateT m s0 = r /\ pre`.
  `Verify w m obs` requires the proposition in `w` to imply the observation
  at every state, precondition, and outcome. This matches the direction in
  [Reader](../Reader/CONTEXT.md), not [ST](../ST/CONTEXT.md).
- The Dijkstra section proves `Verify_ret`, `Verify_bind`, `Verify_get`,
  `Verify_put`, and `Verify_raise`; these feed the `mst` hint database.
  It does not provide a catch verification theorem.

## Incorrectness and examples

`Incorrect presumes achieves w` requires each asserted outcome to have an
initial state satisfying `presumes` and the proposition supplied by `w`.
`IncorrectNormal` restricts this to normal results; `IncorrectErr` to exceptions.
`Incorrect'` conjoins the two. These judgments apply to specifications;
`Verify` transfers their witnesses to the observed computation.

`ReadIfIncWrite.read_if_inc_write` specifies an increment when the initial
state is at least 42 and an exception otherwise. `Verify_read_if_inc_write`
connects it to `Examples.read_if_inc_write`.
`Exists_in_obs_less` witnesses an exception, not a final state;
`Exists_in_obs_more` witnesses normal final states greater than 42.

## Dependencies and boundaries

Read Examples.v first for the computation, then the carrier and observation
in STEx.v before its incorrectness judgments. STEx.v imports Examples.v;
both use ExtLib and Coq arithmetic libraries, and STEx.v uses CoqHammer.
Neither imports Common or Taxonomy. In particular, this sum convention is
the reverse of `A * S + E` in [Common/IOStateExc.v](../Common/IOStateExc.v).
Both local source files are listed in [_CoqProject](../_CoqProject).
