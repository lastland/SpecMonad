# Dijkstra monads context

Parent: [Taxonomy](../Taxonomy/CONTEXT.md). Read [OrderedMonad.v](../Lib/Monad/OrderedMonad.v)
for `MonadMorphism`, `IsMonadMorphism` and `OrderedMonad`, and the
[Triples context](../Triples/CONTEXT.md) for `triple` and the morphisms, first.

[DijkstraMonad.v](DijkstraMonad.v) has the construction, its instances, and
what is and is not a typing; [DijkstraExamples.v](DijkstraExamples.v) has
typed programs. They follow Kenji Maillard et al.,
[*Dijkstra Monads for All*](https://doi.org/10.1145/3341708) (ICFP 2019).

## The construction

For a map `θ : M ~> W` and an order `le` on `W`:

- `DM θ le w := { m : M A | le (θ m) w }`.
- `DMop θ le w := DM θ (flip le) w`, that is `{ m : M A | le w (θ m) }`.

The two types need nothing else. The operations `DM_ret`, `DM_bind`, `DM_wkn`,
`DM_lift` need `θ` to be a monad morphism (`IsMonadMorphism θ`) and its target
to be ordered for the monad and equality of that morphism
(`OrderedTarget θ le`: an `Eq1Equivalence` and an `OrderedMonad`). Both are
found by instance resolution from `θ` and `le`, so
`DM_ret (@dwpSt S) (@ordWSt S) a` needs no further argument. The `DMop`
operations are the `DM` ones at the flipped order, through
`OrderedTarget_flip`, which is `OrderedMonad_flip`; it is not an instance.

The construction satisfies DM4All's laws of a Dijkstra monad. `DM_eq d d'`
compares the underlying computations of `M` and ignores indices and proofs;
`DijkstraLaws θ le` bundles that it is an equivalence respected by `bind`,
the three monad laws, and the three laws of weakening. `DM_laws` proves it
from an `Eq1Equivalence` and a `MonadLawsE` for the source monad, at the
equality the morphism is stated with; `DMop_laws` is the same for `DMop`
(`DijkstraLawsOp`). `Ddwp_laws`, `Ddwp_op_laws`, ... give them for the twelve
named monads. Pass `θ` and `le` explicitly to `DM_laws`: left as holes they
are resolved to the wrong morphism.

## The liftable morphisms

There are 18 `OrderedTarget` instances, one per WP, ASP and DSLP morphism of
[Triples/MonadMorphisms.v](../Triples/MonadMorphisms.v): six readings at the
base, with state, and with state and exceptions. Each names the natural order
of the target:

| Readings | Order |
|---|---|
| `dwp`, `dwlp`, `awp`, `awlp` | `WP_le`, `ordWSt`, `ordWStExc` (reverse implication, lifted) |
| `asp`, `dslp` | `ordASP…`, `ordDSLP…`: pointwise order of the transformers |

The DSP and ASLP morphisms have none. DSP and ASLP are not specification
monads for their natural order, since `bind` is not monotone in its first
argument (`not_OrderedMonad_DSPSt`, `not_OrderedMonad_ASLPSt`), and a
predicate-transformer monad gets a Dijkstra monad from its own order only.
`wpSt_typing_pointwise` and `wpStExc_typing_pointwise` say a typing through a
lifted WP morphism is a family of base typings, one per start state.

## Triples are typings

Stated for any morphism into the target, so for every reading into it:

- WP, all three levels: `triple θ m Under pre post` iff
  `le (θ m) (wpUnder… pre post)`, a typing in `DM`; `triple θ m Over pre post`
  iff `le (wpOver… pre post) (θ m)`, a typing in `DMop`. Keep these argument
  directions: the WP orders are reverse implication.
- ASP `Over`: a typing in `DM` at `aspOver P Q`, the arrow of the relation
  `fun x y => P x -> Q y`.
- DSLP `Under`: a typing in `DMop` at `dslpUnder P Q`, the arrow of
  `fun x y => Q y -> P x`.

`le_aspOver` and `le_dslpUnder` are index-generic; the three levels are the
same statement at three pairs of indices. With state and exceptions the
twelve monads are named `Ddwp`, `Ddwlp`, `Dawp`, `Dawlp`, `Dasp`, `Ddslp`,
and the same with `_op`.

## What is not a typing

- `le_relASP` / `relDSLP_le`: a typing in `DMop` for ASP, and in `DM` for
  DSLP, is an inclusion of the relation the index denotes into the relation
  of the computation.
- `aspUnder P Q` and `dslpOver P Q` are the indices one would like for ASP
  `Under` and DSLP `Over`. A typing there says every start point in `P`
  reaches every result in `Q` (`le_aspUnder`; for DSLP at the complements,
  `dslpOver_le`). It gives the triple when `P` (for DSLP, its complement) is
  inhabited; the DSLP direction uses excluded middle.
- `no_asp_under_index` and `no_dslp_over_index`, with state `nat`: no index
  has the triple as its typings. The three computations `reach0From0`,
  `reach0From1`, `reachNothing` are built by `progOf`, which gives a
  computation a prescribed relation and lets it diverge as well.
- `triple_under_aspPure`: at unit input the ASP `Under` triple is a typing at
  `aspUnder`, for a precondition that holds.

## DijkstraExamples.v

One typed program per WP Dijkstra monad (`progA_Ddwp`, `progRet_Ddwp_op`,
...), `progA_Dasp`, `progEx_Ddslp_op`; `ret_Ddwp` and `put_get_Dawp` use the
operations. For ASP `Under`: `progA_Dasp_op` is a typing, and
`progloom_harder_not_Dasp_op` a triple that is not one. For DSLP `Over`:
`progA_Ddslp`, and `progloom_harder_dslp_over` with
`progloom_harder_not_Ddslp`. `oneOrTwo_Dasp_op` is the stateless case.

## Not here

Choice rules are not part of these modules.
