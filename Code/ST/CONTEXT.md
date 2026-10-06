# ST context

Parent: [Code](../CONTEXT.md). These files use [Common](../Common/CONTEXT.md)'s
state relations, not the generic state-arrow transformer.

[Pred.v](Pred.v) observes `runState m s0 = (r,s1)` with indices initial
state/result/final state. obs' maps to pre/post via p2pp. Verify is
`ordPred (obs m) w`, opposite to Reader/STEx. Correct uses pp2p(pre,post);
Correct' uses ordPrePost. Posts may retain the initial state. Reveal/Incorrect
requires an initial-state witness for each asserted result/final-state pair;
achieves itself hides that initial state. Rule modules include agreement
and primed Correct' rules. OHearnExample's final attempted proof is aborted.

[GuardedPred.v](GuardedPred.v) uses `S -> guarded (S * A)`, with state first.
obsPredForall is universal over guard proofs; obsPredExists needs a witness.
Correct uses the former; Incorrect uses VerifyIncorrect and the latter.
Universal observation can hold vacuously without execution. The final
example deliberately checks the universal observation with VerifyIncorrect,
not the defined existential Incorrect judgment.

Read judgments before rules/examples; for guards also read Common/Guarded.v.
Both built files import Common.v, ExtLib, and CoqHammer.
