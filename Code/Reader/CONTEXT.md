# Reader context

Parent: [Code](../CONTEXT.md). [Reader.v](Reader.v) compares specifications
that retain or hide ExtLib reader environments; lowercase reader is computation.

Reader assigns a result predicate to environment s0 and propositional pre,
with proof that results imply pre. WFReader additionally requires monotonicity;
toReader is its coercion. Return/bind/ask/local supply operation instances;
bind shares the environment and local changes it for its argument. Monad
laws are explicitly unproved.

`obsReader m s0 pre r` is `runReader m s0 = r /\ pre`. Verify requires the
specification to imply the observation, opposite to [ST](../ST/CONTEXT.md).
Verify_ret/bind/ask/local support the mst hint database.

WithStateFreeAchieves.SP existentially hides s0 for each result;
WithStateAwareAchieves.SP retains it and checks asserted environment/result
pairs. Incorrect includes achieves in SP; Correct reverses inclusion.
Weakening, SP_monotone, and agreement require WFReader. The older Incorrect_
has a different quantifier shape, not an alias. Qualified example_3_1r/R
names distinguish computation/specification; Verify connects them.

Read Types → operations/observation → chosen achieved-predicate module.
This built file imports ExtLib, Coq arithmetic, and CoqHammer, not Common or
Taxonomy. Related: [Identity](../Identity/CONTEXT.md), [STEx](../STEx/CONTEXT.md).
