# Identity

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and definitions

These files study incorrectness for pure values and functions, using the
branching `example_3_1` to expose how predicates retain or hide inputs.

[Identity.v](Identity.v) defines `SPost A` as a transformer from a proposition
to a result predicate whose truth implies that proposition. `SPost_ret` and
`theta` observe a pure value. `Incorrect presumes m achieves` requires every
achieved result to belong to that observation. This local `SPost` does not
bundle the monotonicity condition used in [Common](../Common/CONTEXT.md).

## Input context matters

[IdentityVariations.v](IdentityVariations.v) compares three modules:

- `ContextFree.SP P m r` existentially chooses an input `γ` satisfying `P`
  with `m γ = r`; achieved predicates mention only the result.
- `ContextFull.SP P m γ r` retains `γ` and requires `m γ = r /\ P γ`;
  achieved predicates mention both input and result.
- `ContextImplicit.SP P m r` works with a fixed pure value and propositional
  presumption: `m = r /\ P`.

`Incorrect` includes the achieved predicate in `SP`; `Correct`, where
defined, includes `SP` in the postcondition. The context-free and implicit
modules prove weakening, disjunction, monotonicity, and agreement lemmas.
The examples include both successful specifications and proved negations.
The unfinished example in `Identity.v` ends with `Abort`, not a theorem.

## Reading and dependencies

Start with `IdentityVariations.v` for the input-context comparison, then
`Identity.v` for the subset-valued transformer. The former is self-contained;
the latter uses CoqHammer tactics. Both are in [_CoqProject](../_CoqProject).

[Reader](../Reader/CONTEXT.md) makes the environment explicit in a monadic
model; [ST](../ST/CONTEXT.md) adds mutable state and final-state predicates.
