# Base specification order checks

Parent: [base specification monads](../CONTEXT.md).

[SPRelationOrderTests.v](SPRelationOrderTests.v) reuses the relations from
[SPBindOrderCounterexample.v](../SPBindOrderCounterexample.v) to distinguish
relation inclusion from pointwise implication for DSP and ASLP. Both
counterexamples compare specifications whose extracted relations are included,
yet whose transformers fail the corresponding pointwise comparison.

The production order module [SPRelationOrder.v](../SPRelationOrder.v) does
not depend on these witnesses. Its bind-monotonicity results concern relation
inclusion; these tests show why they do not supply pointwise consequence rules.
