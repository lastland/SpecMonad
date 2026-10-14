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
  (`dwp_under_dwlp_under`, ...), eight contrapositives
  (`awp_under_contra_dwlp_over`, ...), and the Galois edges
  `dwlp_under_galois_asp_over`, `awp_over_galois_dslp_under`. No edge has a
  side condition: non-emptiness is part of `divndNE`.
- [InCorrectnessPrinciples.v](../../../../Code/Verification/DivNonDetSt/InCorrectnessPrinciples.v): O'Hearn's
  rewriting rules over the `aspSt` triples, instances of the generic ones, (`Under` is the incorrectness
  triple, `Over` the correctness one): symmetry, consequence, agreement and
  denial, with `_dwlp` variants derived through
  `dwlp_under_galois_asp_over`.
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
