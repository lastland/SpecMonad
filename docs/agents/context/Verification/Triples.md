# Triples context

Parent: [Code](../Code.md). Paper: Section 5. Read [OrderedMonad.v](../../../../Code/Lib/Monad/OrderedMonad.v)
for `MonadMorphism` and `IsMonadMorphism` first, then
[TransformerLaws.v](../../../../Code/Lib/Monad/TransformerLaws.v) and
[ArrowMorphism.v](../../../../Code/Lib/Arrow/ArrowMorphism.v) for the lifts.

[Triple.v](../../../../Code/Verification/Triples/Triple.v) is the general triple. `approxKind` is `Under | Over`;
`SpecReading W A X Y` reads an element of `W A` as a forward (SP) or backward
(WP) transformer between predicates on `X` and on `Y`; `spec_holds w k P Q` is
the judgement on an element; `triple θ m k P Q` is `spec_holds (θ _ m) k P Q`
for a map with an `IsMonadMorphism` instance. `X` and `Y` are parameters,
resolved from `W` and `A`. The second part of the file declares the
`SpecReading` instance of every specification monad the morphisms land in;
the monad files themselves do not mention triples.

The maps the triples are read through are the 24 monad morphisms of
[MonadMorphisms](MonadMorphisms.md): eight readings (`dwp`, `dwlp`, `awp`,
`awlp`, `asp`, `dslp`, `dsp`, `aslp`) at three levels (`xPure`, `xSt`,
`xStExc`). Below, `x` stands for any of the eight.

## MorphismTriples.v

- WP: `triple_xSt` and `triple_xStExc` say a lifted triple is the base
  triple at every start state; `spec_holds_wpSt` / `spec_holds_wpStExc` say
  it for any base map.
- SP: `triple_xPure`, `triple_xSt`, `triple_xStExc` state the triple at each
  level as one judgement (`aspHolds`, `dslpHolds`, `dspHolds`, `aslpHolds`)
  on the base arrow, at indices `(unit, A)`, `(unit * S, A * S)`,
  `(unit * S, option (A * S))`. An SP triple does not split start state by
  start state.
- `xSt_read` / `xStExc_read` unfold a triple to a statement about the
  outcomes `outSt` / `outStExc` of the program.

## TripleTaxonomy.v

The taxonomy diagram of Verscht and Kaminski for one `m : stdivndNE S A`, a
precondition on start states and a postcondition on `A * S`: sixteen
implications (`dwp_under_dwlp_under`, ...), eight contrapositives
(`awp_under_contra_dwlp_over`, ...), and the two Galois edges
`dwlp_under_galois_asp_over` and `awp_over_galois_dslp_under`. The WP half
reduces to the base by the lifting theorem; the SP half reads the four
elements of one relation. No edge has a side condition: non-emptiness is part
of `divndNE`.

The same 26 edges are proved for `m : stdivexcndNE S A` with a postcondition on
`option (A * S)`, under the same names with `_exc`. The base lemmas are used
at the result type `option (A * S)`; nothing else changes.

## Examples.v

`progA`, `progB`, `progRet`, `progEx`, `example_state`, `progloom`, and
`progloom_harder` over `stdivexcndNE`, one verified `triple` for each of the
sixteen kinds, the withdrawal contrast between angelic WP and ASP `Under`,
and O'Hearn's Example 3.1.

## InCorrectnessPrinciples.v

O'Hearn's rewriting rules for a computation with state, `stdivndNE S`, over
the `aspSt` triples (`Under` is the incorrectness triple, `Over` the
correctness one): the two symmetry rules, the two rules of consequence,
agreement and denial. The correctness-side rules have a `_dwlp` variant for
the `dwlpSt` `Under` triples, each derived from its ASP counterpart through
`dwlp_under_galois_asp_over`.

## Cautions

- SP triples do not lift start state by start state; that form is the WP
  one. What lifts on the SP side is the base arrow, re-indexed.
- At unit input DSP coincides with ASP and ASLP with DSLP. The four differ
  from the state level on.
- `Under` puts the transformer's value in the conclusion for both directions:
  a WP `Under` triple is `pre ⊆ wp post`, an SP `Under` triple is
  `post ⊆ sp pre`.
- [Checks/Assumptions.v](../../../../Code/Checks/Assumptions.v) reports the assumptions
  of the morphisms, the lifting theorems, the diagram, and the examples.
