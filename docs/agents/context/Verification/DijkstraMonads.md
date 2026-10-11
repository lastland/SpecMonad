# Dijkstra monads context

Parent: [Code](../Code.md). Paper: Section 6. Read [OrderedMonad.v](../../../../Code/Lib/Monad/OrderedMonad.v)
for `MonadMorphism`, `IsMonadMorphism` and `OrderedMonad`, and the
[MonadMorphisms context](MonadMorphisms.md) for the morphisms, first.

[DijkstraMonad.v](../../../../Code/Verification/DijkstraMonads/DijkstraMonad.v) has the
construction and its instances. It follows Kenji Maillard et al.,
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
[Verification/MonadMorphisms/MonadMorphisms.v](../../../../Code/Verification/MonadMorphisms/MonadMorphisms.v): six readings at the
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

How triples relate to these typings is in
[TriplesAsTypings](TriplesAsTypings.md); nothing here depends on triples.

## Not here

Choice rules are not part of these modules.
