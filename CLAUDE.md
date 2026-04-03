# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Meta rules for this file

- Do NOT add anything easily inferred by Claude Code (file structure, build commands, standard Coq patterns).
- Do NOT add common Coq knowledge.
- Refer to existing docs (`README.md` for project goals/status, `Code/coq-spec-monad.opam` for dependencies) instead of repeating their content.
- If something project-specific warrants a reusable skill, ask the user rather than bloating this file.

## Development rules

- Always look up ITree and ExtLib libraries first before defining something new, to avoid reinventing the wheel.
- Prefer `#[program] Definition` over `refine` for subset types; keep tactics for proof obligations only. This lets Coq insert `proj1_sig` coercions automatically (so you don't write `proj1_sig` everywhere) and generate proof obligations (so you don't explicitly use the `exist` constructor).
- Coq typeclass resolution can cause infinite loops; if you see unusually long compile time, do not wait — try to figure out if there is a typeclass resolution issue. For a project of this size, compilation time should NOT be very long.
  - **Known pattern**: Multiple recursive `#[global] Instance` of the form `Foo ?base → Foo (T ?base)` (e.g., `ArrowChoice_stateArrT` + `ArrowChoice_optionArrT`) cause exponential search. Fix: use explicit `@` references to base instances in instance bodies and proof tactics, bypassing typeclass resolution. See `StateArrowT/Core.v` for the pattern.
  - **`arr_pure_ext` inside `comp_proper` blocks**: Creates unresolvable evars. Pre-assert the equality with `assert (H := ...)` outside the block, then use `exact H` inside.
  - `#[export]` is not supported for `Instance` inside `Section` — use `#[global]`.
  - **Ltac hygiene**: Don't define Ltac if unused or used only once (inline instead). For repeated `unfold` lists within a file, use `Create HintDb db` + `#[local] Hint Unfold ... : db` + `autounfold with db`.

## Architecture: Classes/

`Code/Classes/` defines Hughes-style arrow typeclasses and generic transformer laws:

- `Arrow.v`: Core typeclasses (`Arrow`, `ArrowChoice`, `ArrowApply`, `ArrowLoop`) + laws + `SPArr` (relational arrow) instances.
- `OptionArrowT/`: Generic `optionArrT arr A B := arr A (option B)` transformer. Split into `Core.v` (instances), `ArrowLaws.v`, `ArrowChoiceLaws.v`, `ArrowApplyLaws.v`, `SPArr.v` (concrete). `OptionArrowT.v` is a thin re-export.
- `StateArrowT/`: Generic `stateArrT S arr A B := arr (A*S) (B*S)` transformer. Split into `Core.v`, `ArrowChoiceLaws.v`, `ArrowApplyLaws.v`. `StateArrowT.v` is a thin re-export.

All generic law proofs are purely algebraic — they derive from base arrow laws without inspecting the concrete arrow type.

## Architecture: Taxonomy/

The `Code/Taxonomy/` directory is the core of the project. All monads share the shape `stateT S (optionT <base>)`, varying only in the base monad:

| Base monad | Composed type | File | Role |
|---|---|---|---|
| `itree void1` | `prog` | `Prog.v` | Deterministic computation |
| `PureWP` = `(A -> Prop) -> Prop` | `ProgWP` | `WP.v` | Weakest precondition spec |
| `PureSPost` = `forall pre, {p : A -> Prop \| ...}` | `ProgSPost` | `SPost.v` | Strongest postcondition spec |
| `SetM` = `A -> Prop` | `ndprog` | `NonDetProg.v` | Nondeterministic computation |
| `optionT SetM` (double optionT) | `nditprog` | `NonDetItProg.v` | Nondeterminism + divergence |

**Observation functions** bridge computation monads to specification monads:
- `Observation.v`: maps `prog` to `ProgWP` / `ProgSPost`
- `NonDetObservation.v`: maps `ndprog` to `ProgWP` / `ProgSPost` with demonic/angelic interpretations

**Facts files** (`*Facts.v`) prove monad laws. Generic proofs for `optionT`/`stateT` in `ProgFacts.v` are reused by all composed monads — most higher-level law proofs are just instance chaining.

## CI

See `.github/workflows/SpecMonad.yml` (Coq 8.20, docker-coq-action via opam).

## Build

`Makefile` is gitignored; regenerate with `coq_makefile -f _CoqProject -o Makefile` in `Code/`.
Single file: `make Classes/StateArrowT/Core.vo`. Use `timeout 30 make ...` to catch typeclass loops.
