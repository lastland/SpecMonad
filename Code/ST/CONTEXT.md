# ST

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

ST connects ordinary and guarded state computations to
[Common's relational state specifications](../Common/StateSpecMonads.v).
It defines correctness and incorrectness separately rather than assigning
one implication direction to every verification judgment.

## Ordinary state: Pred.v

[Pred.v](Pred.v) observes ExtLib `state S A` with
`obs m s0 r s1 := runState m s0 = (r, s1)`.
The target `StatePred S A` orders its arguments as initial state, result,
final state. `obs'` converts this relation to a pre/post pair through `p2pp`.

- `Verify w m` is `ordPred (obs m) w`: observed behavior implies the
  specification. [Reader](../Reader/CONTEXT.md) and [STEx](../STEx/CONTEXT.md)
  use the opposite direction for their own `Verify` definitions.
- `Correct` verifies `pp2p (pre, post)`; `Correct'` uses `ordPrePost`
  directly. Both allow the postcondition to mention the initial state.
- `Reveal`, also named `Incorrect`, requires each achieved result/final-state
  pair to have a witnessing initial state satisfying `presumes`.
  Its `achieves : A -> S -> Prop` does not retain that initial state.
- The `ReasoningRulesIncorrectness`, `ReasoningRulesCorrectness`, and
  `ReasoningRulesAgreement` modules provide reasoning rules; primed modules
  cover `Correct'`. `OHearnExample` applies them to a state update.
  Its last attempted example intentionally ends in `Abort`.

## Guarded state: GuardedPred.v

[GuardedPred.v](GuardedPred.v) defines `M S A := S -> guarded (S * A)` using
[Common/Guarded.v](../Common/Guarded.v). The guarded result stores state first,
unlike the `(result, state)` pair in the ordinary observation.

`obsPredForall` universally quantifies over guard proofs; `obsPredExists`
requires a guard proof witnessing the result. `Correct` uses the universal
observation through `Verify`. `Incorrect` uses `VerifyIncorrect` with the
existential observation, requiring both an initial-state witness and a guard proof.

Without a guard proof, `obsPredForall` holds vacuously and does not witness
an execution. The final `example_3_1_incorrect'` deliberately uses that
universal observation with `VerifyIncorrect`, not the defined `Incorrect`.

## Dependencies and reading

Read Pred.v's judgments before its rules and examples. For guarded examples,
read Common/Guarded.v and check which observation the judgment uses.
Both ST files import [Common.v](../Common.v), ExtLib, and CoqHammer, and both
are listed in [_CoqProject](../_CoqProject). They use Common's pre/post orders,
not the generic [state arrow transformer](../Classes/StateArrowT/CONTEXT.md).
