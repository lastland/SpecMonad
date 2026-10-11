# Relational context

Parent: [Code](../CONTEXT.md). Consumers: [SP](../SP/CONTEXT.md),
[MonadRelations](../MonadRelations/CONTEXT.md), [Triples](../Triples/CONTEXT.md),
[Galois connections](../GaloisConnections/CONTEXT.md).

Proof infrastructure with no paper section of its own. The SP arrows prove
their laws through the relation an arrow denotes, the triples read
computations as relations, and `Pred` is used by sections 4, 5 and 7, so
these modules sit below `SP/` in the layering
([layers.txt](../scripts/layers.txt)).

## Files

- [Rel.v](Rel.v): the relational carrier `Rel A B := A -> B -> Prop`, with
  existential composition and pointwise iff equality `Rel_eq` (not Leibniz
  equality). Its fixed-input bind shares the input: `exists b, m i b /\ k b i c`.
  It reuses `Arrow_Rel`, `ArrowChoice_Rel`, `ArrowApply_Rel` and their laws,
  the `optionRel` and `progRelArr` stacks, and relational congruences for
  rewriting. Read its module for exact names during renames.
- [RelSPostArr.v](RelSPostArr.v): the four SP readings of a relation,
  `asp R P b := exists a, P a /\ R a b` and `dslp R P b := forall a, R a b -> P a`,
  with `dspOf` / `aslpOf` their conjunction / disjunction (`aspOf` / `dslpOf`
  are aliases of `asp` / `dslp`). It owns the readings' healthiness, recovery
  (`asp_inv` / `dslp_inv`), inclusion and operation facts. The arrow value is
  the relation, not a relation/transformer pair. At an unreachable output ASP
  is false and DSLP vacuously true; an empty input type has the same effect.
  Determinism alone does not identify the readings: a many-to-one function
  distinguishes them. It adds no carrier, arrow instance or stack law package.
- [RelMonads.v](RelMonads.v) (formerly `SPure.v`): the unit-input relational
  monads, what `ret` and `bind` are relationally, and their orders. Its
  `SPSt` / `SPStExc` are relational monads, unlike the raw SP carriers of the
  same name in [SP/RawSP.v](../SP/RawSP.v).
- [PredMonad.v](PredMonad.v): DM4All's predicate monad `PredM.Pred` and its
  state/option stacks, with `Pred_le` / `ordPredStExc` and
  `OrderedMonad_Pred` / `OrderedMonad_PredStExc`.
- [OptionLoop.v](OptionLoop.v): `optionRel_no_left_tightening` rules out a
  lawful `ArrowLoop` for the `optionRel` operations and pointwise equivalence
  when feedback ranges over all types, including `Empty_set`. Empty feedback
  hides the difference between an empty prefix and one returning `None`.
  [SP/SPostArrEquiv.v](../SP/SPostArrEquiv.v) transports this to the
  property-only option ASP and DSLP arrows. Not in the paper.

Generic relational normalization (`rel_bind`, `relS_bind`, `relO_*`,
`relE_*`) lives in [Lib/Arrow/RelArrowCoherence.v](../Lib/Arrow/RelArrowCoherence.v).
