# Dijkstra monads context

Parent: [Taxonomy](../CONTEXT.md). Read [computation outcomes](../ComputationMonads/CONTEXT.md),
[base specifications and orders](../BaseSpecMonads/CONTEXT.md), and the selected
[WP](../EffectObservations/WP/CONTEXT.md) or [SP](../EffectObservations/SP/CONTEXT.md)
observation first. Coverage follows the three modules in [_CoqProject](../../_CoqProject).

These clients index computations by observations in a selected specification
order, following Kenji Maillard et al., [*Dijkstra Monads for All*](https://doi.org/10.1145/3341708)
(ICFP 2019; DM4all). A carrier, its indexed operations, carrier equations,
and a complete indexed law package are distinct contracts. The declarations
below do not establish every indexed law package or certify assumption-freedom.

## WP clients

[Dijkstra_StDivExcNonDet_WStExc.v](Dijkstra_StDivExcNonDet_WStExc.v) uses the four
`obsDWP` / `obsDWLP` / `obsAWP` / `obsAWLP` observations of `stdivexcnd` into
`WStExc`. Its `ordWStExc` is reverse implication, lifted from `WP_le`:

- `D w := { m : stdivexcnd S A | ordWStExc (obs m) w }`.
- `Dop w` swaps the order arguments: `ordWStExc w (obs m)`.
- `Ddwp`, `Ddwlp`, `Dawp`, `Dawlp` select the four observations; their `_op`
  aliases select `Dop` at the same observations.

The generic construction supplies return, bind, weakening, and lift in both
directions. `orD` supplies a choice rule under a monotone specification
combinator and its observation equation; `Ddwp_or` / `Ddwlp_or` / `Dawp_or` /
`Dawlp_or` instantiate it. Do not infer dual choice rules from the dual aliases.
`D_eq` compares projected computations by `eq1`; `D_bind_ret_l`, `D_bind_ret_r`,
and `D_bind_bind` prove carrier equations, not equality of indexed packages.

`ofTripleSub` / `toTripleSub` bridge `SubsetOf` triples exactly with `D` at
`pp2wp_subset`; `ofTripleSup` / `toTripleSup` bridge `SupersetOf` triples with
`Dop` at `pp2wp_superset`. Keep these argument directions despite the reverse
order. Later clients include liberal divergence typings and compositional examples.

## SP clients and generic construction

Imports in both SP files explicitly choose **earlier `OldMonads/` carriers**,
not the canonical arrow-derived modules with the same names.

- [Dijkstra_StDivExcNonDet_SPStExc.v](Dijkstra_StDivExcNonDet_SPStExc.v) uses
  `stdivexcnd` and its terminating-slice SP observations. Retained outcomes
  have type `option (A * S)`: exceptions remain, outer divergence does not.
  Its `DM` / `DMop` use a selected preorder, inclusion of `eq1` in that order,
  and return/bind observation equations. Indexed sequencing additionally
  requires specification bind monotonicity in both arguments. ASP/DSLP
  instantiate the operations; the file also supplies their choice rules.
- [Dijkstra_StDivNonDet_SPSt.v](Dijkstra_StDivNonDet_SPSt.v) owns the generic
  `EffObs` interface bundling return/bind preservation up to specification
  `eq1`. Despite the filename, its `DM` / `DMop` construction is generic in
  computation and specification monads, using `OrderedMonad` and `EffObs`
  (with specification `Eq1Equivalence`). Both directions have return, bind,
  weakening, and lift. `EffObs_ASP` / `EffObs_DSLP` instantiate it with earlier
  `StASP` / `StDSLP` and `TermSliceObs` of `stdivnd`: observations retain only
  terminating result/state pairs `A * S`, omitting divergence.

In both constructions `DM` requires `obs m <= w`, while `DMop` requires
`w <= obs m`, for the selected order. Qualify repeated names by source module.

## Selected-order bind obstructions

In the exception-capable SP file, `ordDSPStExc_bind_not_mono` and
`ordASLPStExc_bind_not_mono` refute existing-bind first-argument monotonicity
under the global pointwise orders, using actual nat-state programs.
`no_monotone_dsp_bind` / `no_monotone_aslp_bind` also cover alternative binds,
but with these exact hypotheses:

- The candidate has type
  `forall A B, DSPStExc nat A -> (A -> DSPStExc nat B) -> DSPStExc nat B`,
  or the corresponding `ASLPStExc` type, using the earlier carriers.
- For every `x : stdivexcnd nat A` and `f : A -> stdivexcnd nat B`, it satisfies
  `eq1 (obs (x >>= f)) (bnd A B (obs x) (fun a => obs (f a)))`.

Under that observation-preservation hypothesis, the candidate cannot be
monotone in its first argument for the selected pointwise order with a fixed
continuation. These theorems do not require candidate monad laws and do not
exclude every alternative order. `Ddsp` / `Ddsp_op` and `Daslp` / `Daslp_op`
still define indexed carriers; explicit base return, weakening, and lift
operations remain available. See [base order distinctions](../BaseSpecMonads/CONTEXT.md#orders-and-comparisons)
for relation-inclusion orders and separate Boolean-state counterexamples.

## Global triple bridges and their limits

Both SP modules give exact bridges, with no extra precondition side condition:
`ofTripleASPOver` / `toTripleASPOver` connect ASP/`Over` with `Dasp` at
`pp2asp_over`; `ofTripleDSLPUnder` / `toTripleDSLPUnder` connect DSLP/`Under`
with `Ddslp_op` at `pp2dslp_under`. Postconditions range over each module's
retained outcomes, not the raw divergence tokens.

ASP/`Under` is different. In each module, `Dasp_op_under_iff` says global
membership at `pp2asp_under` requires **every** pre-state to reach **every**
post-outcome, whereas the triple asks for **some** pre-state per post-outcome.
The exception-capable file's `toTripleASPUnder` requires an inhabited
precondition; do not turn it into an unconditional equivalence.

Each `no_asp_under_index` fixes nat state, unit result, precondition `True`,
and singleton postcondition at `(tt, 0)` (wrapped in `Some` for the
exception-capable slice). No index in that earlier ASP carrier represents
this triple for all programs via its selected global `DMop` order.
Separately, `ordASPStExcAt_bind_not_mono` / `ordASPStAt_bind_not_mono` refute
continuation-argument bind monotonicity for the fixed-precondition `At` orders.
These counterexamples concern specific carriers, observations, and orders;
they are not a claim that no Dijkstra monad exists under every order.
