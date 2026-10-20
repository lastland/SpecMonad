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
  `ArrowApplyLaws` has four fields: `app_law`
  (`arrow_eq (arr_comp (arr_pure (fun a => (f, a))) arr_app) f`), Hughes'
  `app_pair` (feeding `arr_app` the pairing arrow is the identity) and
  `app_post` (postcomposition passes through `arr_app`), and `app_ext`
  (`arr_app` sees its arrow argument only up to `arrow_eq`).
  Hughes' remaining law, `first (arr (g >>>)) >>> app = second g >>> app`,
  is deliberately absent: `optionArrT`'s composition wraps the continuation
  in `arr_left`, and no arrow law relates `arr_app` to `arr_left` of its
  arrow argument, so that transformer cannot prove it. Nothing needs it.
  The applied forms `app_pair_at` / `app_post_at` / `app_ext_at` at the end
  of the file are what clients use; they are the laws precomposed with a
  pure pair-builder `fun x => (u x, t x)`.
- `ArrowLoop` supplies feedback through `arr_loop`; `ArrowLoopLaws`
  states its tightening, sliding, vanishing, and superposing laws.
- `ArrowT` supplies `arrowT_lift`; the class itself has no preservation laws.
- [ArrowMorphism.v](ArrowMorphism.v) defines `ArrowMorphism arr1 arr2 F` for
  maps `F A B : arr1 A B -> arr2 A B` that respect `arrow_eq` (`morph_proper`,
  a plain field, not an instance) and preserve `arr_pure`, `arr_comp`, and
  `arr_first` up to the target's `arrow_eq`. `ArrowApplyMorphism` adds
  `morph_app`: `F arr_app` is `arr_app` after the arrow in its input is
  converted, `arr_pure (fun p => (F (fst p), snd p))`. The derived operations
  are preserved (`morph_id`, `morph_second`, `morph_split`, `morph_fanout`).
  Preservation of `Monad_Arrow` is `morph_ret_arrow` / `morph_bind_arrow` in
  [SPostArr.v](../Taxonomy/Arrows/SPostArr.v).
- [Galois.v](Galois.v) indexes `Galois` by two binary carriers and both
  orders. `galois_alpha : G A B -> F A B` and `galois_gamma : F A B -> G A B`
  satisfy `le_F A B (galois_alpha g) f <-> le_G A B g (galois_gamma f)`.
  The class includes preorders; derived lemmas give monotonicity,
  `galois_alpha_gamma_deflation`, and `galois_gamma_alpha_inflation`.
- [OrderedMonad.v](OrderedMonad.v) states DM4All's specification-monad
  criterion for unary monads: `OrderedMonad W le` asks for a preorder
  containing `eq1` and a `bind` monotone in both arguments. Every monad is
  ordered by `eq1` (`OrderedMonad_eq1`), so the criterion is relative to `le`.

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
