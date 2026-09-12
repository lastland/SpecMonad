# SP observations context

Parent: [observations](../CONTEXT.md). Targets: [base specs](../../BaseSpecMonads/CONTEXT.md)
and [arrows](../../Arrows/CONTEXT.md).

## Earlier well-formed-monad clients

- StDivExcNonDet_SPStExc selects terminating outcomes of the double-option
  computation, including exceptions, and targets OldMonads' four flavours.
- StDivNonDet_SPStExc/FullOutcomeObs retains the single-option divergence
  outcome; StDivNonDet_SPSt/TermSliceObs selects normal returns only.
- DivNonDet_SPPure/PureObs targets the four pure old carriers;
  RdDivNonDet_RdSPPure applies those observations per reader environment.

For relation R, ASP is existential pre-and-reachability, DSLP universal
reachability-implies-pre, DSP their conjunction, and ASLP their disjunction.
DSP/ASLP target binds recover relations; they are not simple forward composition.
Pure DSP/ASLP collapse to ASP/DSLP, and reader collapse is per environment.
Determinism does not imply unique predecessors, so WP collapse does not imply
SP collapse. Full and terminating-slice observations must not be conflated.

## Arrow-derived clients

SPostArrObservation shares the property-only ASP/DSLP observation interface
and Taxonomy-style judgments. StDivITree_SPostArr, StExcNonDet_SPostArr,
StDivNonDet_SPostArr, and StDivExcNonDet_SPostArr instantiate it using each
computation's outcome relation. RawStOpt_SPostArr shares single-option outcome
facts. Generic relational bind facts and SPostArrMonad select the exact target
arrow dictionaries; neither adds a relation field to property-only values.

SP Over includes observed in asserted post; Under includes asserted in observed.
Old in-monad targets can need an inhabited precondition for ASP Under and an
inhabited complement for DSLP Over. Preserve those hypotheses. Read outcomes
→ selected target/operations → preservation → triples → comparisons/examples.
