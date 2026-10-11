# Verification context

Parent: [Code](Code.md). Paper: the computation monad (Introduction), triples
(Section 5) and Dijkstra monads (Section 6).

Everything that involves the computation monad, split by **setting**:

| Setting | Computation monad | WP target | SP targets | Directory |
|---|---|---|---|---|
| base | `divndNE` | `WPure` | `ASP`, `DSLP`, `DSP`, `ASLP` | [DivNonDet](Verification/DivNonDet.md) |
| state | `stdivndNE S = stateT S divndNE` | `WSt S` | `ASPSt S` … | [DivNonDetSt](Verification/DivNonDetSt.md) |
| state + exceptions | `stdivexcndNE S = stateT S (optionT divndNE)` | `WStExc S` | `ASPStExc S` … | [DivNonDetStExc](Verification/DivNonDetStExc.md) |

What is the same at every setting -- the general triple, the Dijkstra
construction, the comparison of triples with typings at arbitrary indices --
is in [Generic](Verification/Generic.md).

Each setting is a lift of the **base**, not of the previous setting: state
lifts by `stateT`, state and exceptions by `stateT` over `optionT`. So
`DivNonDetSt/` and `DivNonDetStExc/` both import `DivNonDet/` and `Generic/`
and never each other ([layers.txt](../../../Code/scripts/layers.txt)). Every
setting directory has the same files, one per concept:

| File | Contents |
|---|---|
| `Computation.v` | the computation monad (`divndNE`, or its lift) |
| `Morphisms.v` | the eight readings as monad morphisms (at state: lifts of the base ones) |
| `Triples.v` | the specification monads' readings and the triples of the morphisms |
| `TriplesTaxonomy.v` | Verscht and Kaminski's diagram |
| `DijkstraMonads.v` | the Dijkstra monads of the morphisms |
| `Typings.v` | which triples are typings |

plus `InCorrectnessPrinciples.v` in `DivNonDetSt/` and `Examples.v`,
`DijkstraExamples.v` in `DivNonDetStExc/`. File names repeat across settings;
declarations do not, so a qualified name such as `Morphisms.dwpSt` is
unambiguous.

Names follow the same pattern: a lowercase reading followed by the setting,
`dwpPure` / `dwpSt` / `dwpStExc`, and likewise for `dwlp`, `awp`, `awlp`,
`asp`, `dslp`, `dsp`, `aslp` -- 24 monad morphisms, each with an
`IsMonadMorphism` instance. They are monad morphisms and nothing more: the DSP
and ASLP targets are not specification monads.

## Cautions

- `Under` puts the transformer's value in the conclusion for both directions:
  a WP `Under` triple is `pre ⊆ wp post`, an SP `Under` triple is
  `post ⊆ sp pre`.
- SP triples do not lift start state by start state; that form is the WP
  one. What lifts on the SP side is the base arrow, re-indexed.
- At unit input DSP coincides with ASP and ASLP with DSLP; the four differ
  from the state setting on.
- [Checks/Assumptions.v](../../../Code/Checks/Assumptions.v) reports the
  assumptions of the morphisms, the lifting theorems, the diagram, the
  examples and the Dijkstra monads.
