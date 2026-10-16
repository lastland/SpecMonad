# Verification/DivNonDetSt context

Parent: [Verification](../Verification.md). The state setting:
`stdivndNE S = stateT S divndNE`, every object a lift of the base one.

- [Computation.v](../../../../Code/Verification/DivNonDetSt/Computation.v): the stack (ExtLib's `stateT`,
  not defined by hand), lawful by the generic transformer laws
  (`MonadLawsE__stdivndNE`), with `orSt`, `divergeSt` and the outcome lemmas
  `outSt_*`. Programs with state are `stateT S (itree E)` (ExtLib's `get`
  and `put` over ITrees); `denoteSt S := stateT_map S denote`, a monad
  morphism by `MonadMorphism_stateT` (`denoteSt_morphism`), whose outcomes
  from a state are those of the program's tree from it (`outSt_denoteSt`).
- [Morphisms.v](../../../../Code/Verification/DivNonDetSt/Morphisms.v): the lifts. WP: a base morphism
  `σ` lifts to `stateT_map S σ` (`wpSt_morphism`, by `MonadMorphism_stateT`);
  `dwpSt` &c. SP: a base arrow morphism lifts through `state_arrow_morphism`
  (`spSt F`; `spSt_morphism` composes the lifts and inherits the functional
  extensionality of the transformer law packages, `spSt_morphism_rel` goes
  through the relations); `aspSt` &c. The reading of a program is the
  reading of its denotation, `dwpSt S ∘ₘₘ denoteSt S` &c., a monad morphism
  by `IsMonadMorphism_comp`.
- [Triples.v](../../../../Code/Verification/DivNonDetSt/Triples.v): WP: the triple of a lifted morphism is
  the base triple at every start state (`spec_holds_wpSt` for any base map,
  `triple_dwpSt` &c.). SP: the judgement on the base arrow at
  `(unit * S, A * S)` (`triple_aspSt` &c.); an SP triple does not split
  start state by start state. `xSt_read` unfold each triple to the
  outcomes `outSt`.
- [TriplesTaxonomy.v](../../../../Code/Verification/DivNonDetSt/TriplesTaxonomy.v): Verscht and Kaminski's
  diagram for one `m : stdivndNE S A`: sixteen implications
  (`TotalCorr_impl_PartCorr`, ...), eight contrapositives
  (`LisbonLogic_contra_dwlp_over`, ...), and the Galois edges
  `PartCorr_galois_asp_over`, `awp_over_galois_PartIncorr`. No edge has a
  side condition: non-emptiness is part of `divndNE`.
- [InCorrectnessPrinciples.v](../../../../Code/Verification/DivNonDetSt/InCorrectnessPrinciples.v): O'Hearn's
  rewriting rules over the `aspSt` triples, instances of the generic ones, (`Under` is the incorrectness
  triple, `Over` the correctness one): symmetry, consequence, agreement and
  denial, with `_dwlp` variants derived through
  `PartCorr_galois_asp_over`.
- [DijkstraMonads.v](../../../../Code/Verification/DivNonDetSt/DijkstraMonads.v): the `OrderedTarget` instances of
  the lifted morphisms; a typing through a lifted WP morphism is a family of
  base typings (`wpSt_typing_pointwise`).
- [Typings.v](../../../../Code/Verification/DivNonDetSt/Typings.v): with state `nat`, no index has the
  ASP `Under` triple as its typings (`no_asp_under_index`), nor the DSLP
  `Over` triple (`no_dslp_over_index`); the computations `reach0From0`,
  `reach0From1`, `reachNothing` are built by `progOf`.
- [TriplesExamples/ITreePrograms.v](../../../../Code/Verification/DivNonDetSt/TriplesExamples/ITreePrograms.v):
  `progA_IT` (set the state to `42`, then keep it or add `1`, choosing with
  ITree's `Or`): its tree is a choice between the two results
  (`progA_IT_tree`, up to `eutt`), hence its outcomes (`progA_IT_out`) and
  its DWP and ASP `Under` triples.
- [HealthyReadings.v](../../../../Code/Verification/DivNonDetSt/HealthyReadings.v): the stateful
  readings land in the stateful WP variants (`dwpSt_DWPSt_morphism` &c.), as
  `stateT_map` of the base corestrictions.
- [TripleRules.v](../../../../Code/Verification/DivNonDetSt/TripleRules.v): the sequencing rules.
  WP triples compose under and over for any monad morphism into `WSt S`
  (`wpSt_bind_under`, `wpSt_bind_over`), so for all eight kinds; ASP and DSLP compose in
  both directions, the over-approximate rules with the side condition
  `q0 => p_a` and the under-approximate ones with `p_a => q0`;
  under-approximate ASP and over-approximate DSLP also need an inhabited
  result type; under-approximate DSP and over-approximate ASLP compose
  through their components.
- [TriplesExamples/ResetEven.v](../../../../Code/Verification/DivNonDetSt/TriplesExamples/ResetEven.v):
  the paper's running program (reset to 0 from an even state): its AWP and
  ASP readings, Lisbon logic failing where incorrectness logic holds, and
  its AWP specification as a Dijkstra-monad typing.
- [TriplesExamples/DSPSequencing.v](../../../../Code/Verification/DivNonDetSt/TriplesExamples/DSPSequencing.v):
  Figure 2: over-approximate DSP and under-approximate ASLP triples do not
  compose; the incorrectness-logic rule needs its side condition the other
  way (`side_aspSt_under`) and an inhabited result type
  (`inhabited_aspSt_under`).
- [TriplesExamples/IncorrectnessLogic.v](../../../../Code/Verification/DivNonDetSt/TriplesExamples/IncorrectnessLogic.v):
  the sequential examples of O'Hearn's *Incorrectness Logic* (POPL 2020),
  with each triple the paper states proved, or refuted when the paper calls
  it wrong. First the language: `prog S = optionT (stateT S (itree ILE))`,
  so an `error()` keeps its state (the state-and-exceptions setting drops
  it, and cannot state `er:` assertions); `assume false` diverges.
  The triples are the named logics on the denotation `denoteIL C`
  (`IncorrLogic`, `PartCorr`, `TotalCorr`, `LisbonLogic`); `ok q`/`er q` the
  result assertions. `outIL_*` compute outcomes construct by construct,
  `il_simpl` chains them for straight-line code, `outIL_iter` reduces a loop
  to the base loop rules, and `starIL_ok`/`starIL_er` are Iterate zero and
  non-zero. Then the examples, one module per part of the paper:
  `UnderApproximation` (§3), `ProofRules` (§4, Fact 9), `Loops`
  (Figure 5), `Conditionals` (Figures 6, 7), `Flaky` (Figure 8),
  `Composition` (Figure 9).
