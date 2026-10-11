# Monad morphisms context

Parent: [Code](../Code.md). Paper: Sections 5 and 6. Read
[OrderedMonad.v](../../../../Code/Lib/Monad/OrderedMonad.v) for `MonadMorphism`
and `IsMonadMorphism` first, then
[TransformerLaws.v](../../../../Code/Lib/Monad/TransformerLaws.v) and
[ArrowMorphism.v](../../../../Code/Lib/Arrow/ArrowMorphism.v) for the lifts.
Consumers: [Triples](Triples.md) (a triple is a morphism followed by a reading)
and [DijkstraMonads](DijkstraMonads.md) (a Dijkstra monad indexes programs by
their image under a morphism).

[MonadMorphisms.v](../../../../Code/Verification/MonadMorphisms/MonadMorphisms.v)
defines one set of 24 monad morphisms out of the non-empty base `divndNE` or
one of its two transformer stacks, all three defined in
[DivNonDetNE.v](../../../../Code/Verification/Computation/DivNonDetNE.v). The
maps are monad morphisms and nothing more: the DSP and ASLP targets are not
specification monads.

| Level | Computation | WP target | SP targets |
|---|---|---|---|
| base | `divndNE` | `WPure` | `ASP`, `DSLP`, `DSP`, `ASLP` |
| state | `stdivndNE S` | `WSt S` | `ASPSt S` and the other three |
| state + exceptions | `stdivexcndNE S` | `WStExc S` | `ASPStExc S` and the other three |

Names: a lowercase reading followed by the level, `dwpPure` / `dwpSt` /
`dwpStExc`, and likewise for `dwlp`, `awp`, `awlp`, `asp`, `dslp`, `dsp`,
`aslp`. Below, `x` stands for any of the eight.

- WP: `dwpPure`, `dwlpPure`, `awpPure`, `awlpPure : divndNE A -> WPure A`,
  each a `MonadMorphism`. The state maps are `stateT_map S σ` and the
  state+exception ones `stateT_map S (optionT_map σ)`, morphisms by
  `MonadMorphism_stateT` / `MonadMorphism_optionT`. They land in `WPure`,
  not in the four WP variants.
- SP: `sliceNE` keeps the terminating outcomes; `outcomes0`, `outcomesSt`,
  `outcomesStExc` read a `Pred` stack as an element of the relation stack.
  `spPure F`, `spSt F`, `spStExc F` apply a base arrow morphism `F` out of
  `Rel`, lifted by `state_arrow_map` / `option_arrow_map`; the four readings
  are the four choices of `F`.
- Each SP morphism statement has two proofs. `x*_morphism` composes the
  lifts (`arrow_morphism_monad`, `state_arrow_morphism`,
  `state_option_arrow_morphism`) and, above the base, inherits the functional
  extensionality of the transformer law packages. `x*_morphism_rel` goes
  through the relations denoted: closed for ASP and DSLP, excluded middle for
  DSP and ASLP. The `IsMonadMorphism` instances use the `_rel` proofs, so a
  triple or a Dijkstra monad depends on no more than those.
- At input `unit` DSP coincides with ASP and ASLP with DSLP; the four differ
  from the state level on.
