# STEx

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and result layout

This directory studies forward specifications for deterministic state with
exceptions. [Examples.v](Examples.v) defines `read_inc_write` and
`read_if_inc_write` in ExtLib's `stateT nat (sum unit)`.

[STEx.v](STEx.v) defines the specification `STEx S E A`: for an initial
state and propositional precondition, it assigns each `E + A * S` result
a proposition that implies the precondition.

- `inl e` is an exception with no final state; `inr (a, s)` is normal return.
- `retSTEx`, `bindSTEx`, `getSTEx`, `putSTEx`, `raiseSTEx`, and `catchSTEx`
  provide monad/state/exception operations. Bind propagates exceptions;
  catch invokes its handler at the original initial state.
- The file provides operation instances but explicitly leaves monad laws
  unproved. It does not bundle a monotonicity condition in the carrier.
- `obsSTEx` combines equality with `runStateT` and the supplied precondition.
  `Verify w m obs` requires the specification to imply the observation.
  The proved compositional rules cover return, bind, get, put, and raise.

## Incorrectness and examples

`Incorrect` asks every achieved sum result to have a witnessing initial
state satisfying `presumes`. `IncorrectNormal` restricts this to normal
results; `IncorrectErr` restricts it to exceptions. `Incorrect'` conjoins
those two obligations.

The `ReadIfIncWrite` module defines a specification with the same program
shape as `Examples.read_if_inc_write`. It proves normal/error incorrectness
claims, `Verify_read_if_inc_write`, and existence results in the observation.

## Reading and dependencies

Read `Examples.v`, then the carrier and observation in `STEx.v`, then
`ReadIfIncWrite`. Both files are listed in [_CoqProject](../_CoqProject);
`STEx.v` imports `Examples.v` and uses ExtLib, CoqHammer, and Coq arithmetic.

[ST](../ST/CONTEXT.md) uses ordinary state and a different `Verify` direction.
[Reader](../Reader/CONTEXT.md) uses the same underapproximation direction.
[Common/IOStateExc.v](../Common/IOStateExc.v) uses `(A * S) + E` instead,
so its exception tag is on the other side of the sum; see
[Common context](../Common/CONTEXT.md).
