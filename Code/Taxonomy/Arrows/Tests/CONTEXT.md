# Concrete arrow instance checks

Parent: [Arrows context](../CONTEXT.md). Related:
[semantic examples](../Examples/CONTEXT.md),
[generic Classes tests](../../../Classes/Tests/CONTEXT.md).

Start with [ArrowMonadInstances.v](ArrowMonadInstances.v): named `Monad`,
`Eq1Equivalence`, and `MonadLawsE` dictionaries specialize
[ArrowMonad.v](../../../Classes/ArrowMonad.v). Agreement lemmas compare compact
return/bind formulas with the exact derived operations. Resolution checks cover
concrete specification arrows, both SP presentations, and base/option/state/
state-over-option layers with non-unit inputs. The named stacks from
[SPostArrMonad.v](../SPostArrMonad.v) use explicit generic law witnesses.

[ArrowTransformerInstances.v](ArrowTransformerInstances.v) checks `optionRel`,
the monad-view `progRelM` / `nditRelM` stacks, coupled option/state stacks, and
double-option application laws. It depends on the generic arrow transformers
and [TransformerLaws.v](../../ComputationMonads/TransformerLaws.v).
Its `PropertyEquality` module checks that property-only equality is
definitionally pointwise transformer iff, resolves all three base law packages,
and exercises `app_ext` and `Proper_bind` with semantic hypotheses for ASP and
DSLP. The double-option exact equalities use the explicit bundled-equality
bridges after applying the semantic application law.
Plain definitions register no helper instances: `:= _` checks automatic
resolution; explicit generic applications check specialization.

The generic contract is tested in
[ArrowMonadRegression.v](../../../Classes/Tests/ArrowMonadRegression.v), including
an application satisfying the fixed-arrow law but breaking monad right identity.
This directory checks that concrete specification instances use that contract.
