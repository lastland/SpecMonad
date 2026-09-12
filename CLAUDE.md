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

## Architecture

Start with [CONTEXT-MAP.md](CONTEXT-MAP.md), then read the relevant directory contexts. See [Classes](Code/Classes/CONTEXT.md) for generic arrow contracts and [Taxonomy](Code/Taxonomy/CONTEXT.md) for computation/specification boundaries. The [Taxonomy README](Code/Taxonomy/README.md) gives detailed semantics and naming conventions.

All generic arrow-transformer law proofs are purely algebraic — they derive from base arrow laws without inspecting the concrete arrow type. Qualify shared names such as `ASPostArr` and `DSLPostArr` when the property-only and coupled presentations are both in scope.

`Taxonomy/deprecated/` holds earlier iterations that are deliberately excluded from `_CoqProject`; ignore them when grepping for symbol references.

## CI

See `.github/workflows/SpecMonad.yml` (Coq 8.20, docker-coq-action via opam).

## Build

`Makefile` is gitignored; regenerate with `coq_makefile -f _CoqProject -o Makefile` in `Code/`.
Single file: `make Classes/StateArrowT/Core.vo`. Use `timeout 30 make ...` to catch typeclass loops.

## Agent skills

### Issue tracker

Use GitHub issues in `lastland/SpecMonad`; external PRs are not a
triage surface. See [docs/agents/issue-tracker.md](docs/agents/issue-tracker.md).

### Triage labels

Use the five default triage labels. See [docs/agents/triage-labels.md](docs/agents/triage-labels.md).

### Domain docs

Use the multi-context layout: start with [CONTEXT-MAP.md](CONTEXT-MAP.md), then read
the relevant per-directory contexts. See [docs/agents/domain.md](docs/agents/domain.md).
