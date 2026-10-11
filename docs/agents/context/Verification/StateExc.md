# Verification/StateExc context

Parent: [Verification](../Verification.md). The state-and-exceptions
setting: `stdivexcndNE S = stateT S (optionT divndNE)`, a lift of the base
(not of the state setting). Outer `None` is divergence, `Some None` an
exception, `Some (Some (a, s))` a normal return; an exception has no final
state. The SP morphisms keep exceptions and omit divergence.

- [ComputationStExc.v](../../../../Code/Verification/StateExc/ComputationStExc.v): the stack, with
  `orStExc`, `divergeStExc`, `raiseStExc`, `pickStExc` and `outStExc_*`.
- [MorphismsStExc.v](../../../../Code/Verification/StateExc/MorphismsStExc.v): WP lifts
  `stateT_map S (optionT_map σ)` (`wpStExc_morphism`); SP lifts through
  `state_option_arrow_morphism` (`spStExc F`); `dwpStExc`, `aspStExc` &c.
- [TriplesStExc.v](../../../../Code/Verification/StateExc/TriplesStExc.v): as with state, at the result
  type `option (A * S)` (`triple_dwpStExc`, `triple_aspStExc`, `xStExc_read`).
- [TripleTaxonomyStExc.v](../../../../Code/Verification/StateExc/TripleTaxonomyStExc.v): the same 26
  edges for `m : stdivexcndNE S A`, under the same names with `_exc`.
- [Examples.v](../../../../Code/Verification/StateExc/Examples.v): `progA`, `progB`, `progRet`,
  `progEx`, `example_state`, `progloom`, `progloom_harder`, one verified
  triple for each of the sixteen kinds, the contrast between angelic WP and
  ASP `Under`, and O'Hearn's Example 3.1.
- [DijkstraStExc.v](../../../../Code/Verification/StateExc/DijkstraStExc.v): the `OrderedTarget`
  instances and the twelve named Dijkstra monads `Ddwp`, `Ddwlp`, `Dawp`,
  `Dawlp`, `Dasp`, `Ddslp` and their `_op` variants, with their laws.
- [TypingsStExc.v](../../../../Code/Verification/StateExc/TypingsStExc.v): the WP typings at this
  setting (`triple_under_wpStExc`, ...).
- [DijkstraExamples.v](../../../../Code/Verification/StateExc/DijkstraExamples.v): one typed program per
  WP Dijkstra monad, `progA_Dasp`, `progEx_Ddslp_op`; for ASP `Under`,
  `progA_Dasp_op` is a typing and `progloom_harder_not_Dasp_op` a triple
  that is not one; for DSLP `Over`, `progloom_harder_not_Ddslp`.
