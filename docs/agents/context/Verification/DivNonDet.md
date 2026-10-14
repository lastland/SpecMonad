# Verification/DivNonDet context

Parent: [Verification](../Verification.md). The base setting: `divndNE`.

- [Computation.v](../../../../Code/Verification/DivNonDet/Computation.v) starts with the programs: ITrees
  `itree E A` over any events, read as nondeterministic: an event may get
  any of its answers. `HasAnswers E` (every event has an answer) holds for
  ITree's `nondetE` and is closed under `+'`; the facts about the paths of
  a tree are in [Lib/ITreeFacts.v](../../../../Code/Lib/ITreeFacts.v). It then builds the base monad of
  outcomes in three steps.
  `SetM A := A -> Prop` is a set of outcomes; `divnd` is `optionT SetM`,
  with `None` divergence and `divergeD`, and no `MonadExc` instance; its
  outcome law `outcomes_bind` is a constructive pointwise `<->`, not an
  equality of computations. `divndNE` is the fragment with at least one
  outcome (`retNE`, `bindNE`, `orNE`, `divergeNE`). An empty outcome set is
  blocking, neither a return nor divergence: `divndNE` excludes it, it does
  not require termination (`empty_prefix_blocks`, `diverge_survives_empty`
  check this on `divnd`). The equality is Leibniz equality of outcome sets,
  so the laws use functional and propositional extensionality.
  Iteration: `iterNE` (the `MonadIter divndNE` instance) has the outcomes
  `iterOutcomes`, the finite runs `iterOut` (inductive: the body exits or
  diverges after finitely many iterations) and the infinite runs
  `loopsForever` (coinductive, read as divergence). ITree's `iter_Prop` is
  the inductive part alone, under which an infinite loop has no outcome.
  The loop rules are stated on the body's outcome relation:
  `iterOut_invariant` (DWLP, ASP Over), `loopsForever_variant` (DWP),
  `iterOut_reach` (AWP, ASP Under), `loopsForever_recurrence` (AWLP). They
  are closed; non-emptiness of a loop (`iterOutcomes_nonEmpty`) uses
  excluded middle.
  Last, `denote : itree E A -> divndNE A` maps a program to the values it
  may return (`Leaf`) and divergence if it has an infinite path
  (`any_infinite`): a monad morphism up to `eutt` (`denote_morphism`)
  that maps `ITree.iter` to `iterNE` (`denote_iter`);
  `denote_vis` reads an event, `denote_or` ITree's `Nondeterminism.or`,
  `denote_spin` the silent loop. Every tree has an outcome by excluded
  middle (`leaf_or_infinite`); ITree and paco add `eq_rect_eq`.
- [Morphisms.v](../../../../Code/Verification/DivNonDet/Morphisms.v): the eight readings, each
  defined once here. WP: `dwpPure`, `dwlpPure`, `awpPure`, `awlpPure :
  divndNE A -> WPure A`, from `demonicWP` / `angelicWP`; they land in
  `WPure`, not in the WP variants. SP: `sliceNE` keeps the terminating
  outcomes, `termRel` reads them as a relation, and `spPure F` applies a
  base arrow morphism `F` out of `Rel` ([SP/SPostArrEquiv.v](../../../../Code/SP/SPostArrEquiv.v));
  `aspPure` &c. are its four instances. Each SP morphism has two proofs:
  `x_morphism` by the lifts, `x_morphism_rel` through the relations denoted
  (closed for ASP and DSLP, excluded middle for DSP and ASLP); the
  `IsMonadMorphism` instances use the `_rel` proofs. The reading of a
  program is the reading of its denotation, `dwpPure ∘ₘₘ denote` &c., a
  monad morphism by `IsMonadMorphism_comp`.
- [Triples.v](../../../../Code/Verification/DivNonDet/Triples.v): `SpecReading` of `WPure`, `ASP`,
  `DSLP`, `DSP`, `ASLP`; `triple_aspPure` &c., the SP triple at indices
  `(unit, A)`; and each reading in terms of the outcomes (`dwpPure_read`
  &c.), an SP precondition being the proposition `P tt`.
- [TriplesTaxonomy.v](../../../../Code/Verification/DivNonDet/TriplesTaxonomy.v): the WP edges between
  the base readings of one computation, and the Galois edges with the
  terminating outcomes (`galois_slice_dwlpPure`, `galois_awpPure_slice`).
- [DijkstraMonads.v](../../../../Code/Verification/DivNonDet/DijkstraMonads.v): the `OrderedTarget` instances of
  the WP, ASP and DSLP base morphisms.
- [Typings.v](../../../../Code/Verification/DivNonDet/Typings.v): without state the ASP `Under`
  triple is a typing at `aspUnder`, for a precondition that holds
  (`triple_under_aspPure`); `oneOrTwo_Dasp_op`.
- [TriplesTaxonomy.v](../../../../Code/Verification/DivNonDet/TriplesTaxonomy.v) also states the Galois
  edge as an equivalence of triples without state,
  `dwlp_under_galois_asp_over_pure`.
- [InCorrectnessPrinciples.v](../../../../Code/Verification/DivNonDet/InCorrectnessPrinciples.v):
  O'Hearn's rules for the `aspPure` triples (`first_symmetry_rule_aspPure`,
  ..., `principle_of_denial_aspPure`), and their `dwlpPure` variants through
  that edge.
- [TriplesExamples/](../../../../Code/Verification/DivNonDet/TriplesExamples): loops and ITree
  programs. `Loops.v`: `forever m` and `silentLoop` have no finite run, so
  DWLP accepts them and DWP rejects them; `dwp_no_loops`. `Countdown.v`:
  `countdown n` terminates from `0`, loops forever from `1`, and may do
  either from `2` up; its outcomes (`countdown_out`) by the four loop rules,
  and one triple of each of the sixteen kinds, the input `n` being a
  parameter since the only start point is `tt`. `ITreePrograms.v`: programs
  with ITree's definitions over `nondetE`: `oneOrTwoIT` (a choice by
  `Nondeterminism.or`), `ITree.spin` (DWLP accepts it, DWP rejects it), and
  `countdownIT n` with `ITree.iter`, which has the outcomes of `countdown n`
  and so exactly its triples, for each reading (`countdownIT_dwp` &c.).
