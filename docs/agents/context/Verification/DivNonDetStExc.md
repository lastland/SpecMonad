# Verification/DivNonDetStExc context

Parent: [Verification](../Verification.md). The state-and-exceptions
setting: `stdivexcndNE S = stateT S (optionT divndNE)`, a lift of the base
(not of the state setting). Outer `None` is divergence, `Some None` an
exception, `Some (Some (a, s))` a normal return; an exception has no final
state. The SP morphisms keep exceptions and omit divergence.

- [Computation.v](../../../../Code/Verification/DivNonDetStExc/Computation.v): the stack, with
  `orStExc`, `divergeStExc`, `raiseStExc`, `pickStExc` and `outStExc_*`.
- [Morphisms.v](../../../../Code/Verification/DivNonDetStExc/Morphisms.v): WP lifts
  `stateT_map S (optionT_map σ)` (`wpStExc_morphism`); SP lifts through
  `state_option_arrow_morphism` (`spStExc F`); `dwpStExc`, `aspStExc` &c.
- [Triples.v](../../../../Code/Verification/DivNonDetStExc/Triples.v): as with state, at the result
  type `option (A * S)` (`triple_dwpStExc`, `triple_aspStExc`, `xStExc_read`).
- [TriplesTaxonomy.v](../../../../Code/Verification/DivNonDetStExc/TriplesTaxonomy.v): the same 26
  edges for `m : stdivexcndNE S A`, under the same names with `_exc`.
- [Examples.v](../../../../Code/Verification/DivNonDetStExc/Examples.v): `progA`, `progB`, `progRet`,
  `progEx`, `example_state`, `progloom`, `progloom_harder`, one verified
  triple for each of the sixteen kinds, the contrast between angelic WP and
  ASP `Under`, and O'Hearn's Example 3.1.
- [DijkstraMonads.v](../../../../Code/Verification/DivNonDetStExc/DijkstraMonads.v): the `OrderedTarget`
  instances and the twelve named Dijkstra monads `Ddwp`, `Ddwlp`, `Dawp`,
  `Dawlp`, `Dasp`, `Ddslp` and their `_op` variants, with their laws.
- [Typings.v](../../../../Code/Verification/DivNonDetStExc/Typings.v): the WP typings at this
  setting (`triple_under_wpStExc`, ...).
- [DijkstraExamples.v](../../../../Code/Verification/DivNonDetStExc/DijkstraExamples.v): one typed program per
  WP Dijkstra monad, `progA_Dasp`, `progEx_Ddslp_op`; for ASP `Under`,
  `progA_Dasp_op` is a typing and `progloom_harder_not_Dasp_op` a triple
  that is not one; for DSLP `Over`, `progloom_harder_not_Ddslp`.
