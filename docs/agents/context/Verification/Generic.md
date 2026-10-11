# Verification/Generic context

Parent: [Verification](../Verification.md). What is the same at every setting.

- [Triple.v](../../../../Code/Verification/Generic/Triple.v): the general triple. `approxKind` is
  `Under | Over`; `SpecReading W A X Y` reads an element of `W A` as a
  forward (SP) or backward (WP) transformer between predicates on `X` and on
  `Y`; `spec_holds w k P Q` is the judgement on an element; `triple θ m k P Q`
  is `spec_holds (θ _ m) k P Q` for a map with an `IsMonadMorphism` instance.
  `X` and `Y` are resolved from `W` and `A`. The SP judgements `aspHolds`,
  `dslpHolds`, `dspHolds`, `aslpHolds` are stated on a base arrow at
  arbitrary indices: every SP triple at every setting is one of them.
- [DijkstraMonad.v](../../../../Code/Verification/Generic/DijkstraMonad.v): for a map `θ : M ~> W` and
  an order `le` on `W`, `DM θ le w := { m : M A | le (θ m) w }` and
  `DMop θ le w := DM θ (flip le) w`. The operations `DM_ret`, `DM_bind`,
  `DM_wkn`, `DM_lift` need `IsMonadMorphism θ` and `OrderedTarget θ le`
  (an `Eq1Equivalence` and an `OrderedMonad`), both found by instance
  resolution. `DM_laws` / `DMop_laws` prove DM4All's laws; pass `θ` and
  `le` explicitly to `DM_laws`: left as holes they are resolved to the wrong
  morphism. The `DMop` operations go through `OrderedTarget_flip`, which is
  not an instance. Follows Maillard et al.,
  [*Dijkstra Monads for All*](https://doi.org/10.1145/3341708) (ICFP 2019).
- [TripleTaxonomy.v](../../../../Code/Verification/Generic/TripleTaxonomy.v): the four SP readings of
  one relation, at arbitrary indices -- the SP edges of the diagram.
- [Typings.v](../../../../Code/Verification/Generic/Typings.v): which triples are typings, for any
  morphism into the target. WP: `triple θ m Under pre post` iff
  `le (θ m) (wpUnder… pre post)`, a typing in `DM`; `Over` a typing in
  `DMop` at `wpOver…` (keep these directions: the WP orders are reverse
  implication). ASP `Over` is a typing in `DM` at `aspOver P Q`, DSLP
  `Under` one in `DMop` at `dslpUnder P Q` (`le_aspOver`, `le_dslpUnder`).
  Not typings: `le_relASP` / `relDSLP_le` (a typing is an inclusion of
  relations); at `aspUnder` / `dslpOver` a typing says every start point
  reaches every result (`le_aspUnder`, `dslpOver_le`), which gives the
  triple when the precondition is inhabited (`aspUnder_typing_triple`) and
  is vacuous when it is empty.
- [InCorrectnessPrinciples.v](../../../../Code/Verification/Generic/InCorrectnessPrinciples.v): O'Hearn's
  rewriting rules (symmetry, consequence, agreement, denial) for
  `aspHolds R` on any relation `R`. Every ASP triple is such a judgement, so
  each setting instantiates them.
