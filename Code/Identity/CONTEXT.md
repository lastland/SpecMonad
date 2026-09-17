# Identity

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

Identity studies correctness and incorrectness for Coq values and functions.
Its examples show how retaining or hiding an input changes the assertion
that an achieved result is possible. There is no effect-transformer stack here.

## Established vocabulary and contracts

[Identity.v](Identity.v) defines `SPost A` as a precondition-indexed result
predicate whose outputs imply that precondition. It has no monotonicity field.
`theta m` is `SPost_ret m`; `Incorrect presumes m achieves` means
`forall r, achieves r -> r = m /\ presumes`.
The `example_3_1` tests illustrate this fixed-value reading. The final attempted
test ends in `Abort`, not a proved negative result.

[IdentityVariations.v](IdentityVariations.v) separates three readings of `SP`
(strongest postcondition) into modules:

- `ContextFree.SP P m r` is `exists γ, m γ = r /\ P γ`.
  `Incorrect` requires each achieved result to have some suitable input;
  the input need not be the same for different results.
- `ContextFull.SP P m γ r` is `m γ = r /\ P γ`.
  Achieved predicates retain the input, and `Incorrect` checks every asserted
  input/result pair rather than choosing an input witness.
- `ContextImplicit.SP P m r` is `m = r /\ P`, with `P : Prop` and `m : A`.
  Any program inputs are parameters outside this definition, as in Identity.v.

In `ContextFree` and `ContextImplicit`, `Incorrect` uses implication from
the achieved predicate to `SP`; `Correct` uses implication from `SP` to the
postcondition. `Correct_alt` gives the direct correctness reading.
`Incorect_weaken`, `Incorect_disj`, and `agreement` state the corresponding
reasoning rules; retain the source spelling `Incorect` when locating them.

## Dependencies and boundaries

Read IdentityVariations first to choose the intended treatment of inputs.
Its examples prove both positive and negated incorrectness assertions;
do not transfer one module's result to another without checking the quantifiers.
[Reader](../Reader/CONTEXT.md) explores a related distinction for environments.

Neither file imports Common, Reader, or Taxonomy. Identity.v imports CoqHammer;
IdentityVariations.v has no explicit imports. The local `SPost` is not an alias
of [Common's monotone carrier](../Common/PureSpecMonads.v).
Both files appear in [_CoqProject](../_CoqProject).
