# Verification/Base context

Parent: [Verification](../Verification.md). The base setting: `divndNE`.

- [DivNonDetNE.v](../../../../Code/Verification/Base/DivNonDetNE.v) builds the base monad in three steps.
  `SetM A := A -> Prop` is a set of outcomes; `divnd` is `optionT SetM`,
  with `None` divergence and `divergeD`, and no `MonadExc` instance; its
  outcome law `outcomes_bind` is a constructive pointwise `<->`, not an
  equality of computations. `divndNE` is the fragment with at least one
  outcome (`retNE`, `bindNE`, `orNE`, `divergeNE`). An empty outcome set is
  blocking, neither a return nor divergence: `divndNE` excludes it, it does
  not require termination (`empty_prefix_blocks`, `diverge_survives_empty`
  check this on `divnd`). The equality is Leibniz equality of outcome sets,
  so the laws use functional and propositional extensionality.
- [MorphismsPure.v](../../../../Code/Verification/Base/MorphismsPure.v): the eight readings, each
  defined once here. WP: `dwpPure`, `dwlpPure`, `awpPure`, `awlpPure :
  divndNE A -> WPure A`, from `demonicWP` / `angelicWP`; they land in
  `WPure`, not in the WP variants. SP: `sliceNE` keeps the terminating
  outcomes, `termRel` reads them as a relation, and `spPure F` applies a
  base arrow morphism `F` out of `Rel` ([SP/SPostArrEquiv.v](../../../../Code/SP/SPostArrEquiv.v));
  `aspPure` &c. are its four instances. Each SP morphism has two proofs:
  `x_morphism` by the lifts, `x_morphism_rel` through the relations denoted
  (closed for ASP and DSLP, excluded middle for DSP and ASLP); the
  `IsMonadMorphism` instances use the `_rel` proofs.
- [TriplesPure.v](../../../../Code/Verification/Base/TriplesPure.v): `SpecReading` of `WPure`, `ASP`,
  `DSLP`, `DSP`, `ASLP`; `triple_aspPure` &c., the SP triple at indices
  `(unit, A)`.
- [TripleTaxonomyPure.v](../../../../Code/Verification/Base/TripleTaxonomyPure.v): the WP edges between
  the base readings of one computation, and the Galois edges with the
  terminating outcomes (`galois_slice_dwlpPure`, `galois_awpPure_slice`).
- [DijkstraPure.v](../../../../Code/Verification/Base/DijkstraPure.v): the `OrderedTarget` instances of
  the WP, ASP and DSLP base morphisms.
- [TypingsPure.v](../../../../Code/Verification/Base/TypingsPure.v): without state the ASP `Under`
  triple is a typing at `aspUnder`, for a precondition that holds
  (`triple_under_aspPure`); `oneOrTwo_Dasp_op`.
