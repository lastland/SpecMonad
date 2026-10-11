# Triples as typings context

Parent: [Code](../Code.md). Paper: Section 6. Builds on
[Triples](Triples.md) and [DijkstraMonads](DijkstraMonads.md), which both read
the same [monad morphisms](MonadMorphisms.md) and do not depend on each other.

[TriplesAsTypings.v](../../../../Code/Verification/TriplesAsTypings/TriplesAsTypings.v)
compares the two: which triples are typings in a Dijkstra monad and which are
not. [DijkstraExamples.v](../../../../Code/Verification/TriplesAsTypings/DijkstraExamples.v)
types the programs of [Triples/Examples.v](../../../../Code/Verification/Triples/Examples.v)
and contrasts them with their triples.

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

