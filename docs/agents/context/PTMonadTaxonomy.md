# PTMonadTaxonomy context

Parent: [Code](Code.md). Paper: Section 4 (taxonomy of predicate
transformer monads, Figure 1). Builds on [WP](WP.md),
[SP](SP.md), [Relational](Relational.md) and
[MonadRelation.v](../../../Code/Lib/Monad/MonadRelation.v); used by
[Triples](Verification.md). The [design notes](../../design.md)
give the longer story.

The directory is named after Section 4's title, "Taxonomy of Predicate
Transformer Monads" (PT = predicate transformer). "Taxonomy" names two things
in the code: this directory, whose [MonadTaxonomy.v](../../../Code/PTMonadTaxonomy/MonadTaxonomy.v) has the
edges of Figure 1, and [Verification/DivNonDetSt/TriplesTaxonomy.v](../../../Code/Verification/DivNonDetSt/TriplesTaxonomy.v),
Verscht and Kaminski's taxonomy of triples (Section 4.1) for monadic
programs. The relations themselves are monadic relations in the sense of
[Lib/Monad/MonadRelation.v](../../../Code/Lib/Monad/MonadRelation.v).

## Files in reading order

- [TransformerRelations.v](../../../Code/PTMonadTaxonomy/TransformerRelations.v) (§4.1): the monotone
  carrier `MonotoneSPost` read with either index fixed, as `MonoPT` (first
  index: SP; second: WP), and the three relations of Verscht and Kaminski's
  taxonomy on bare transformers: `pt_le` (implication), `Contrapositive`, and
  `GaloisPT`. `pt_under` / `pt_over` are the two triple readings of a
  transformer. Contrapositive facts that turn a negated statement back into a
  positive one are classical.
- [MonotoneSPSt.v](../../../Code/PTMonadTaxonomy/MonotoneSPSt.v): monotone stateful SP transformers
  `SPStMon` with an angelic and a demonic monad structure, each lawful only up
  to an inequation (`lunitStrictlyLax`: monotone sps alone are not a lawful
  monad, paper Introduction and §3.2). `Ladj` / `Radj` relate them to `WSt`,
  with representability by `PredSt`.
- [SPStBindComparisons.v](../../../Code/PTMonadTaxonomy/SPStBindComparisons.v): the state bind of each SP
  monad read as a monotone stateful transformer and compared with the
  `SPStMon` structures. Not in the paper.
- [Carriers.v](../../../Code/PTMonadTaxonomy/Carriers.v): the carriers of the SP and WP
  monads inside `MonoPT` — the second index one state at a time, the first
  along `S ~ unit * S` — the four refinements, the broad monads, the WP and SP
  variants inside them, the pure level, duals under `Contrapositive`, and
  adjoints.
- [MonadTaxonomy.v](../../../Code/PTMonadTaxonomy/MonadTaxonomy.v) (§4.2, §4.4): implication,
  contrapositive and Galois connection as monadic relations
  ([MonadRelation.v](../../../Code/Lib/Monad/MonadRelation.v)) on `WPure` and its
  transformer stacks, on `SPStMon` with its angelic and demonic structures,
  and between the variant monads at the pure, state and state-option levels.
  `Section Flavours` has the edges of Figure 1
  (`MonadRelation_dwp_implies_dwlp`, …, `MonadRelation_contra_*`,
  `MonadRelation_galois_*`); the file ends with the stateless collapse
  (`MonadRelation_dsp_asp_pure`, `MonadRelation_aslp_dslp_pure`).
  `Section PureImplications` has the base sp implication edges of
  Figure 1(a), ASLP -> ASP and DSLP -> DSP, through the parts; without
  state every ASP element implies every ASLP element, and every DSP element
  every DSLP element (`asp_implies_aslp_any_pure`,
  `dsp_implies_dslp_any_pure`).

- `MonadTaxonomy.v`, section `PureImplications` (Figure 1(a)): the base sp
  implication edges ASLP -> ASP and DSLP -> DSP through the parts; without
  state every ASP element implies every ASLP element
  (`asp_implies_aslp_any_pure`).

## Cautions

- DSP and ASLP enter SP implications through one part (`aspOf` / `dslpOf`),
  because their `bind` does not preserve the pointwise orders (paper's
  asterisks in Figure 1).
- `GaloisSPWP` / `GaloisWPSP` are `Ladj` / `Radj`.
  Name the angelic or demonic `SPStMon` structure explicitly.
- Every variant instance that involves an SP monad goes through the relation
  the SP element denotes: implication is inclusion and contrapositive is
  equality of the denoted relations, each one index-generic lemma. A Galois
  instance is the base relation between `PredM.Pred` and `WPure`
  (`GaloisPredWP`, `GaloisWPPred`), lifted by the monad transformers on the
  WP side and read at the denoted results on the SP side
  (`MonadRelation_rel_pred` and its two stack versions). The Galois instances
  use no axiom.
- Healthiness, monad equations, precondition monotonicity and ordered bind
  are separate. Over/Under SP and WP triples can reverse implication and
  argument order: inspect the local definitions.
- §4.3 (category-theoretic insights) has no code.
