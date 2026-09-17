# Classes

Parent: [Code context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Purpose and scope

Classes defines Hughes-style arrow interfaces, their laws, generic option/state
transformers, and a binary Galois-connection class. Concrete specification
carriers belong to [Taxonomy arrows](../Taxonomy/Arrows/CONTEXT.md).
[Common/Classes.v](../Common/Classes.v) defines a separate pre/post-order API.

## Established vocabulary and contracts

- [Arrow.v](Arrow.v) defines `Arrow` through `arr_pure`, `arr_comp`, and
  `arr_first`. `arr_comp f g` runs `f` before `g`; `arr_first` acts on the
  first component of a pair. `arr_id`, `arr_second`, `arr_split`, and
  `arr_fanout` are derived operations.
- `ArrowEq` selects an equivalence `arrow_eq`. `ArrowLaws` states the
  composition and product laws, with `comp_proper` and `first_proper`
  requiring operations to respect that equivalence.
- `ArrowChoice` supplies `arr_left` on sums; `ArrowChoiceLaws` includes
  branch, composition, naturality, and product-distribution laws.
- `ArrowApply` supplies `arr_app : arr (arr A B * A) B`.
  On main, `ArrowApplyLaws` contains only `app_law`:
  `arrow_eq (arr_comp (arr_pure (fun a => (f, a))) arr_app) f`.
  Do not assume additional application or extensionality fields.
- `ArrowLoop` supplies feedback through `arr_loop`; `ArrowLoopLaws`
  states its tightening, sliding, vanishing, and superposing laws.
- `ArrowT` supplies `arrowT_lift`; the class itself has no preservation laws.
- [Galois.v](Galois.v) indexes `Galois` by two binary carriers and both
  orders. `galois_alpha : G A B -> F A B` and `galois_gamma : F A B -> G A B`
  satisfy `le_F A B (galois_alpha g) f <-> le_G A B g (galois_gamma f)`.
  The class includes preorders; derived lemmas give monotonicity,
  `galois_alpha_gamma_deflation`, and `galois_gamma_alpha_inflation`.

## Transformers and boundaries

[OptionArrowT.v](OptionArrowT.v) and [StateArrowT.v](StateArrowT.v) re-export
their implementation modules. Read the [option](OptionArrowT/CONTEXT.md) or
[state](StateArrowT/CONTEXT.md) context for each transformer's prerequisites.
Their proofs use base arrow laws and equalities of helper functions, without
inspecting a concrete specification carrier. Neither provides loop lifting.

The relational carrier is `PredArr A B := A -> B -> Prop` in
[PredArr.v](../Taxonomy/Arrows/PredArr.v), not in `Arrow.v`.
The generic `Monad_Arrow` construction remains in `Section ArrowMonad` of
[SPostArr.v](../Taxonomy/Arrows/SPostArr.v), not in a separate Classes module.
Concrete binary adjunctions live in [GaloisArr.v](../Taxonomy/Arrows/GaloisArr.v).

Start with `Arrow.v`, then the relevant transformer or `Galois.v`.
Classes imports Coq libraries and, in the option implementation, CoqHammer;
it does not import Common or Taxonomy. All local implementation modules and
both re-exports are listed in [_CoqProject](../_CoqProject).
