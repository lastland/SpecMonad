# ST

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and ordinary state

This directory connects deterministic state computations and guarded state
computations to the relational specifications in [Common](../Common/CONTEXT.md).

[Pred.v](Pred.v) observes ExtLib `state S A` through
`obs m s0 r s1 := runState m s0 = (r, s1)`, using
[`StatePred S A`](../Common/StateSpecMonads.v).
`obs'` maps that relation to a pre/post pair.

- `Verify w m` means `ordPred (obs m) w`: the observed behavior implies the
  specification. This is the opposite implication direction from `Verify`
  in [Reader](../Reader/CONTEXT.md) and [STEx](../STEx/CONTEXT.md).
- `Correct` uses `pp2p (pre, post)`; `Correct'` uses `ordPrePost` directly.
  Their postconditions can mention initial state, result, and final state.
- `Reveal`, also exposed as `Incorrect`, requires each achieved result and
  final state to have a witnessing initial state satisfying `presumes`.
  Achieved predicates have type `A -> S -> Prop`, hiding the initial state.
- The reasoning-rule modules prove correctness/incorrectness rules and
  agreement/denial principles. `OHearnExample` applies them to a state update;
  its intentionally unfinished example ends with `Abort`.

## Guarded state

[GuardedPred.v](GuardedPred.v) defines `M S A := S -> guarded (S * A)` using
[Common/Guarded.v](../Common/Guarded.v). Its guarded result stores state first,
whereas ExtLib's ordinary state result stores the return value first.

`obsPredForall` universally quantifies over guard proofs; `obsPredExists`
requires a witness. `Correct` uses the former, while `Incorrect` applies
`VerifyIncorrect` to the latter. Without a guard proof, the universal formula
can hold vacuously, so these observations are not interchangeable. The final
example explicitly contrasts an incorrectness-style check using the universal
observation with the existential definition.

## Reading and build membership

Start with `Pred.v` through `Reveal`, then its rule modules and examples.
Read `GuardedPred.v` alongside `Common/Guarded.v` for the proof quantifiers.
Both files import [Common.v](../Common.v), use ExtLib and CoqHammer, and are
listed in [_CoqProject](../_CoqProject).
