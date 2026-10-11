# Verification context

Parent: [Code](Code.md). Paper: the computation monad (Introduction), triples
(Section 5) and Dijkstra monads (Section 6).

Everything that involves the computation monad, split by **setting**:

| Setting | Computation monad | WP target | SP targets | Directory |
|---|---|---|---|---|
| base | `divndNE` | `WPure` | `ASP`, `DSLP`, `DSP`, `ASLP` | [Base](Verification/Base.md) |
| state | `stdivndNE S = stateT S divndNE` | `WSt S` | `ASPSt S` … | [State](Verification/State.md) |
| state + exceptions | `stdivexcndNE S = stateT S (optionT divndNE)` | `WStExc S` | `ASPStExc S` … | [StateExc](Verification/StateExc.md) |

What is the same at every setting -- the general triple, the Dijkstra
construction, the comparison of triples with typings at arbitrary indices --
is in [Generic](Verification/Generic.md).

Each setting is a lift of the **base**, not of the previous setting: state
lifts by `stateT`, state and exceptions by `stateT` over `optionT`. So
`State/` and `StateExc/` both import `Base/` and `Generic/` and never each
other ([layers.txt](../../../Code/scripts/layers.txt)). Every setting has the
same files, named by concept and suffixed by the setting as the identifiers
are (`Pure`, `St`, `StExc`):

| Concept | Base | State | StateExc |
|---|---|---|---|
| computation monad | `DivNonDetNE.v` | `ComputationSt.v` | `ComputationStExc.v` |
| the eight readings as monad morphisms | `MorphismsPure.v` | `MorphismsSt.v` | `MorphismsStExc.v` |
| triples of those morphisms | `TriplesPure.v` | `TriplesSt.v` | `TriplesStExc.v` |
| Verscht and Kaminski's diagram | `TripleTaxonomyPure.v` | `TripleTaxonomySt.v` | `TripleTaxonomyStExc.v` |
| Dijkstra monads | `DijkstraPure.v` | `DijkstraSt.v` | `DijkstraStExc.v` |
| triples as typings | `TypingsPure.v` | `TypingsSt.v` | `TypingsStExc.v` |
| examples, rules | -- | `InCorrectnessPrinciples.v` | `Examples.v`, `DijkstraExamples.v` |

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
