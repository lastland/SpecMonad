# Concrete arrow instance checks

Parent: [Arrows context](../CONTEXT.md). Related:
[semantic examples](../Examples/CONTEXT.md),
[generic Classes tests](../../../Classes/Tests/CONTEXT.md).

Start with [SPostArrInfrastructure.v](SPostArrInfrastructure.v) for the
standalone property-only arrow checks. It imports no BaseSpecMonads module and
checks `ArrowLaws`, `ArrowChoiceLaws`, and `ArrowApplyLaws` for all four flavours
implemented in [SPostArr.v](../SPostArr.v). Its semantic regressions distinguish
DSP composition from raw forward transformer composition and exercise binary
state-over-option bind at a non-unit input, retaining that input, threading
the intermediate state, and propagating `None` without a final state.

[ArrowMonadInstances.v](ArrowMonadInstances.v) checks named `Monad`,
`Eq1Equivalence`, and `MonadLawsE` dictionaries that specialize
[ArrowMonad.v](../../../Classes/ArrowMonad.v). Agreement lemmas compare compact
return/bind formulas with the exact derived operations. Resolution checks cover
`Rel`, the property-only ASP/DSLP carriers, and the other specification arrows,
including base/option/state/state-over-option layers with non-unit inputs.
The relational coverage serves both `asp` and `dslp` readings of the same
carrier; neither reading needs its own monad dictionary. The state-over-option
monad dictionaries of `ASPMonad.v` and `DSLPMonad.v` use explicit generic law
witnesses. `CanonicalSP` in `ArrowMonadInstances.v` compares canonical and
compatibility application/bind, checks dictionary identity, and exercises a
state update followed by propagated failure, read through the compatibility
relation `ASP_rel`.

[ArrowTransformerInstances.v](ArrowTransformerInstances.v) checks `optionRel`,
relational state-over-option arrows, the monad-view `progRelM` / `nditRelM`
stacks, and double-option application laws. Both SP readings reuse the existing
`Rel` operations and generic stack laws. The file depends on the generic arrow
transformers and [TransformerLaws.v](../../ComputationMonads/TransformerLaws.v).

Its `PropertyEquality` module checks that property-only equality is
definitionally pointwise transformer iff, resolves all three base law packages,
and exercises `app_ext` and `Proper_bind` with semantic hypotheses for ASP and
DSLP. `Rel` keeps `Rel_eq`. The [semantic examples](../Examples/CONTEXT.md)
exercise the direct-Rel conversions and their higher-order application behavior.
Plain definitions register no helper instances: `:= _` checks automatic
resolution; explicit generic applications check specialization.

`LiftLaws` resolves all three lift contracts for option over Rel, double
option, and state over option, with selected dictionaries. It checks the
explicit lift-to-morphism bridge and rewrites with lift composition under
pointwise Rel equality. ASP/DSLP clients use pointwise transformer iff for
lift properness/composition without reflecting it into ordinary equality.

The generic contract is tested in
[ArrowMonadRegression.v](../../../Classes/Tests/ArrowMonadRegression.v), including
an application satisfying the fixed-arrow law but breaking monad right identity.
This directory checks that concrete specification instances use that contract.
