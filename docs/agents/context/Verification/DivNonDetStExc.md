# Verification/DivNonDetStExc context

Parent: [Verification](../Verification.md). The state-and-exceptions
setting: `stdivexcndNE S = stateT S (optionT divndNE)`, a lift of the base
(not of the state setting). Outer `None` is divergence, `Some None` an
exception, `Some (Some (a, s))` a normal return; an exception has no final
state. The SP morphisms keep exceptions and omit divergence.

- [Computation.v](../../../../Code/Verification/DivNonDetStExc/Computation.v): the stack, with
  `orStExc`, `divergeStExc`, `raiseStExc`, `pickStExc` and `outStExc_*`.
  Programs with state and exceptions are `stateT S (optionT (itree E))`
  (ExtLib's `get`, `put` and `raise` over ITrees); `denoteStExc S :=
  stateT_map S (optionT_map denote)`, a monad morphism by
  `MonadMorphism_optionT` and `MonadMorphism_stateT`
  (`denoteStExc_morphism`); `outStExc_denoteStExc` gives its outcomes.
- [Morphisms.v](../../../../Code/Verification/DivNonDetStExc/Morphisms.v): WP lifts
  `stateT_map S (optionT_map σ)` (`wpStExc_morphism`); SP lifts through
  `state_option_arrow_morphism` (`spStExc F`); `dwpStExc`, `aspStExc` &c.
  The reading of a program is the reading of its denotation,
  `dwpStExc S ∘ₘₘ denoteStExc S` &c., by `IsMonadMorphism_comp`.
- [Triples.v](../../../../Code/Verification/DivNonDetStExc/Triples.v): as with state, at the result
  type `option (A * S)` (`triple_dwpStExc`, `triple_aspStExc`, `xStExc_read`).
- [TriplesTaxonomy.v](../../../../Code/Verification/DivNonDetStExc/TriplesTaxonomy.v): the same 26
  edges for `m : stdivexcndNE S A`, under the same names with `_exc`.
- [TriplesExamples.v](../../../../Code/Verification/DivNonDetStExc/TriplesExamples.v): the index, with
  the table of one verified triple for each of the sixteen kinds; it exports
  one file per example in [TriplesExamples/](../../../../Code/Verification/DivNonDetStExc/TriplesExamples),
  each holding the program, its outcome lemma and its triples: `ProgA.v`,
  `ProgB.v`, `ProgRet.v`, `ProgEx.v`, `Withdrawal.v` (`progloom`,
  `progloom_harder`: the contrast between angelic WP and ASP `Under`),
  `IL2020.v` (Example 3.1 of O'Hearn, POPL 2020), `ITreePrograms.v` (`progA` as an
  ITree program, `progA_IT`, with the outcomes of `progA` and two of its
  triples), `Counter.v` (`counter N`, an ITree loop that stops or
  increments and raises on reaching `N`: its outcomes by `denote_iter` and
  the base loop rules (`counter_out`); a reachable bug, every state below
  `N` reached, dropping paths, and the principle of denial refuting the
  correctness triples; incorrectness against Lisbon logic; total
  correctness below `N` and divergence from `N` on), and `Common.v`
  (`preEq0`, `postEq0`).
- [DijkstraMonads.v](../../../../Code/Verification/DivNonDetStExc/DijkstraMonads.v): the `OrderedTarget`
  instances and the twelve named Dijkstra monads `Ddwp`, `Ddwlp`, `Dawp`,
  `Dawlp`, `Dasp`, `Ddslp` and their `_op` variants, with their laws.
- [Typings.v](../../../../Code/Verification/DivNonDetStExc/Typings.v): the WP typings at this
  setting (`triple_under_wpStExc`, ...).
- [DijkstraExamples.v](../../../../Code/Verification/DivNonDetStExc/DijkstraExamples.v): one typed program per
  WP Dijkstra monad, `progA_Dasp`, `progEx_Ddslp_op`; for ASP `Under`,
  `progA_Dasp_op` is a typing and `progloom_harder_not_Dasp_op` a triple
  that is not one; for DSLP `Over`, `progloom_harder_not_Ddslp`.
- [InCorrectnessPrinciples.v](../../../../Code/Verification/DivNonDetStExc/InCorrectnessPrinciples.v):
  O'Hearn's rules for the `aspStExc` triples (`..._aspStExc`), and their
  `dwlpStExc` variants through `PartCorr_galois_asp_over_exc`.
