# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Meta rules for this file

- Do NOT add anything easily inferred by Claude Code (file structure, build commands, standard Coq patterns).
- Do NOT add common Coq knowledge.
- Refer to existing docs (`README.md` for project goals/status, `Code/coq-spec-monad.opam` for dependencies) instead of repeating their content.
- If something project-specific warrants a reusable skill, ask the user rather than bloating this file.

## Development rules

- Use **well-formed** / **well-formedness** for the properties constraining SP transformers.
- Always look up ITree and ExtLib libraries first before defining something new, to avoid reinventing the wheel.
- Do not use proof mode for definitions; write explicit terms. Prefer `#[program] Definition` over `refine` for subset types, and keep tactics for proof obligations only. This lets Coq insert `proj1_sig` coercions automatically (so you don't write `proj1_sig` everywhere) and generate proof obligations (so you don't explicitly use the `exist` constructor).
- Coq typeclass resolution can cause infinite loops; if you see unusually long compile time, do not wait — try to figure out if there is a typeclass resolution issue. For a project of this size, compilation time should NOT be very long.
  - **Known pattern**: Multiple recursive `#[global] Instance` of the form `Foo ?base → Foo (T ?base)` (e.g., `ArrowChoice_stateArrT` + `ArrowChoice_optionArrT`) cause exponential search. Fix: use explicit `@` references to base instances in instance bodies and proof tactics, bypassing typeclass resolution. See `StateArrowT/Core.v` for the pattern.
  - **`arr_pure_ext` inside `comp_proper` blocks**: Creates unresolvable evars. Pre-assert the equality with `assert (H := ...)` outside the block, then use `exact H` inside.
  - `#[export]` is not supported for `Instance` inside `Section` — use `#[global]`.
  - **Ltac hygiene**: Don't define Ltac if unused or used only once (inline instead). For repeated `unfold` lists within a file, use `Create HintDb db` + `#[local] Hint Unfold ... : db` + `autounfold with db`.
  - **CoqHammer in proof bodies**: Always use `sauto limit: 200` (not bare `sauto`) — bare `sauto` loops on typeclass-heavy goals. Works well for propositional tails after manual preprocessing (`unfold`/`cbn`/`destruct`). Keep manual proofs for witness construction (pair/sum `exists`), `rewrite` with `IsASP_rewrite`/`IsDSLP_rewrite`, `Proper_bind` setoid reasoning, and typeclass-derived `reflexivity`/`transitivity`. No global limit option exists — limits are per-tactic only.
- **Sort inference in match bodies**: A bare `forall r, ... -> post r` as the body of a `match` against `mkOptionT` / `mkRelSPPair` has its sort inferred as `Type`, not `Prop`, breaking `optionT PureWP` / `Pred` unification with a confusing universe error. Wrap in a connective (`/\`, `\/`, `exists`) or add a `(_ : Prop)` cast.
- **Classical `itree void1` termination**: Reasoning that a deterministic ITree either converges or diverges requires `eutt_reta_or_div`, `ret_not_div`, `any_infinite_proper_eutt` from `ITree.Extra.Dijkstra.PureITreeBasics` — *not* in the default `From ITree Require Import ITree Eq Props.Infinite.`. `ret_not_div` takes `A` and `E` implicit, so call it as `ret_not_div Hinf`, not `ret_not_div _ _ _ Hinf`.

## Architecture: Classes/

`Code/Classes/` defines Hughes-style arrow typeclasses and generic transformer laws:

- `Arrow.v`: Core typeclasses (`Arrow`, `ArrowChoice`, `ArrowApply`, `ArrowLoop`) + laws + `Pred` (relational arrow, `A -> B -> Prop`) instances.
- `OptionArrowT/`: Generic `optionArrT arr A B := arr A (option B)` transformer. Split into `Core.v`, `ArrowLaws.v`, `ArrowChoiceLaws.v`, `ArrowApplyLaws.v`. `OptionArrowT.v` is a thin re-export. Concrete `optionPred` instances now live in `Taxonomy/Pred.v`.
- `StateArrowT/`: Generic `stateArrT S arr A B := arr (A*S) (B*S)` transformer. Split into `Core.v`, `ArrowChoiceLaws.v`, `ArrowApplyLaws.v`. `StateArrowT.v` is a thin re-export.

All generic law proofs are purely algebraic — they derive from base arrow laws without inspecting the concrete arrow type.

## Architecture: Taxonomy/

The `Code/Taxonomy/` directory is the core of the project. All monads share the shape `stateT S (optionT <base>)`, varying only in the base monad:

| Base monad | Composed type | File | Role |
|---|---|---|---|
| `itree void1` | `prog` | `Prog.v` | Deterministic computation |
| `PureWP` = `(A -> Prop) -> Prop` | `ProgWP` | `WP.v` | Weakest precondition spec |
| `SetM` = `A -> Prop` | `ndprog` | `NonDetProg.v` | Nondeterministic computation |
| `optionT SetM` (double optionT) | `nditprog` | `NonDetItProg.v` | Nondeterminism + divergence |

`Arrows/SPostArr.v` defines property-only strongest-postcondition arrows (`PureASPostArr`, `PureDSLPostArr`); `Arrows/RelSPPairArr.v` defines the coupled presentation (`PureRelASPPairArr`, `PureRelDSLPPairArr`). See `Code/Taxonomy/README.md` for their well-formedness properties, operation-preserving equivalence, and transformer stacks. Qualify shared names such as `ASPostArr` and `DSLPostArr` when both presentations are in scope.

**Observation functions** bridge computation monads to specification types (both WP and SP):
- `Observation.v`: maps `prog` to 4 SP variants (`obsASP` / `obsDSLP` / `obsDSP` / `obsASLP`) and 4 WP variants (`obsAWP` / `obsDWP` / `obsAWLP` / `obsDWLP`), with `obsWPCollapse` / `obsWLPCollapse` showing angelic-demonic collapse under determinism
- `NonDetObservation.v`: maps `ndprog` to `ASPostArr` (SP) and `ProgWP` (demonic/angelic WP)
- `NonDetItObservation.v`: maps `nditprog` to `ASPostArr` (SP) and `ProgWP` (4 WP variants)

`ComputationMonads/TransformerLaws.v` provides generic monad-transformer laws. Each SP arrow presentation proves its core arrow laws; the corresponding `*Coherence.v` module proves the additional application-coherence laws.

`WPArr.v` defines the reader-WP Kleisli arrow `WPArr A B := A -> PureWP B`; laws in `WPArrFacts.v` hold definitionally (all `reflexivity`). `RelPrePost.v` defines `RelPrePost A B := (A -> Prop) -> (A -> B -> Prop) -> Prop` — a "validator" of Hoare specs that embeds `WPArr` injectively. `Galois.v` establishes Galois connections (via Dijkstra refinement order) among `Pred`, `PrePost`, `WPArr`, and `RelPrePost`.

`Taxonomy/deprecated/` holds earlier iterations that are deliberately excluded from `_CoqProject`; ignore them when grepping for symbol references.

## CI

See `.github/workflows/SpecMonad.yml` (Coq 8.20, docker-coq-action via opam).

## Build

`Makefile` is gitignored; regenerate with `coq_makefile -f _CoqProject -o Makefile` in `Code/`.
Single file: `make Classes/StateArrowT/Core.vo`. Use `timeout 30 make ...` to catch typeclass loops.
