# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Meta rules for this file

- Do NOT add anything easily inferred by Claude Code (file structure, build commands, standard Coq patterns).
- Do NOT add common Coq knowledge.
- Refer to existing docs (`README.md` for project goals/status, `Code/coq-spec-monad.opam` for dependencies) instead of repeating their content.
- If something project-specific warrants a reusable skill, ask the user rather than bloating this file.

## Development rules

- Reserve **healthy** / **healthiness** for predicate transformers and their class-defining conditions from refinement calculus and related literature. Use **well-formed** / **well-formedness** for general validity constraints; healthiness does not assert algebraic arrow or monad laws.
- Always look up ITree and ExtLib libraries first before defining something new, to avoid reinventing the wheel.
- Do not use proof mode for definitions; write explicit terms. Prefer `#[program] Definition` over `refine` for subset types, and keep tactics for proof obligations only. This lets Coq insert `proj1_sig` coercions automatically (so you don't write `proj1_sig` everywhere) and generate proof obligations (so you don't explicitly use the `exist` constructor).
- Coq typeclass resolution can cause infinite loops; if you see unusually long compile time, do not wait — try to figure out if there is a typeclass resolution issue. For a project of this size, compilation time should NOT be very long.
  - **Known pattern**: Multiple recursive `#[global] Instance` of the form `Foo ?base → Foo (T ?base)` (e.g., `ArrowChoice_stateArrT` + `ArrowChoice_optionArrT`) cause exponential search. Fix: use explicit `@` references to base instances in instance bodies and proof tactics, bypassing typeclass resolution. See `StateArrowT/Core.v` for the pattern.
  - **`arr_pure_ext` inside `comp_proper` blocks**: Creates unresolvable evars. Pre-assert the equality with `assert (H := ...)` outside the block, then use `exact H` inside.
  - `#[export]` is not supported for `Instance` inside `Section` — use `#[global]`.
  - **Ltac hygiene**: Don't define Ltac if unused or used only once (inline instead). For repeated `unfold` lists within a file, use `Create HintDb db` + `#[local] Hint Unfold ... : db` + `autounfold with db`.
  - **CoqHammer in proof bodies**: Always use `sauto limit: 200` (not bare `sauto`) — bare `sauto` loops on typeclass-heavy goals. Works well for propositional tails after manual preprocessing (`unfold`/`cbn`/`destruct`). Keep manual proofs for witness construction (pair/sum `exists`), `rewrite` with `IsASP_rewrite`/`IsDSLP_rewrite`, `Proper_bind` setoid reasoning, and typeclass-derived `reflexivity`/`transitivity`. No global limit option exists — limits are per-tactic only.
- **Sort inference in match bodies**: A bare `forall r, ... -> post r` as the body of a `match` against `mkOptionT` has its sort inferred as `Type`, not `Prop`, breaking `optionT PureWP` unification with a confusing universe error. Wrap in a connective (`/\`, `\/`, `exists`) or add a `(_ : Prop)` cast.
- **Classical `itree void1` termination**: Reasoning that a deterministic ITree either converges or diverges requires `eutt_reta_or_div`, `ret_not_div`, `any_infinite_proper_eutt` from `ITree.Extra.Dijkstra.PureITreeBasics` — *not* in the default `From ITree Require Import ITree Eq Props.Infinite.`. `ret_not_div` takes `A` and `E` implicit, so call it as `ret_not_div Hinf`, not `ret_not_div _ _ _ Hinf`.

## Architecture

Read [CONTEXT-MAP.md](CONTEXT-MAP.md), then the parent and local contexts
relevant to the task. These describe the current source contracts and build
boundaries. `Backup/` (including `Backup/Taxonomy-deprecated/`) is excluded from `_CoqProject`; omit it from
normal symbol searches.

Concrete arrow instantiation checks live in `Taxonomy/Arrows/Tests/`.

All generic arrow-transformer law proofs are purely algebraic — they derive from base arrow laws without inspecting the concrete arrow type. Relational SP arrows reuse `Rel` and its existing laws and stacks; `RelSPostArr.v` computes the `asp` / `dslp` readings. The property-only equivalences use `ASP_rel` / `relASP` and `DSLP_rel` / `relDSLP` directly. Their round trips and morphisms use the selected pointwise equalities through `ArrowMorphism`, not Leibniz law dictionaries or relational equality reflection. The local exact source substitution in loop-obstruction transport is separate; see the [Arrows context](Code/SP/CONTEXT-arrows.md).

## Agent skills

### Issue tracker

GitHub Issues (`lastland/SpecMonad`); external PRs are not a triage surface.
See [docs/agents/issue-tracker.md](docs/agents/issue-tracker.md).

### Triage labels

Use the five canonical triage labels without renaming.
See [docs/agents/triage-labels.md](docs/agents/triage-labels.md).

### Domain docs

`Arrows/SPostArr.v` implements all four property-only binary SP arrows. The
four flavour monads and the unary `SPostArrMonad.v` bridge in `BaseSpecMonads/`
consume it; `SPostArr.v` must not depend on that directory, including `SPure.v`.
`Rel.v` owns the relation carrier and stacks; `RelSPostArr.v` owns their four SP
readings. See `Code/Taxonomy/README.md` for healthiness conditions, equivalences,
and stacks. Qualify shared names, especially binary and unary accessors.

Multi-context: the root map links to contexts for active Coq directories.
See [docs/agents/domain.md](docs/agents/domain.md).

`ComputationMonads/TransformerLaws.v` provides generic monad-transformer laws. Each SP arrow presentation proves its core arrow laws and derives its base application coherence from `Lib/Arrow/RelArrowCoherence.v`; the generic arrow transformers lift the full law contract.


## CI

See `.github/workflows/SpecMonad.yml` (Coq 8.20, docker-coq-action via opam).

## Build

`Code/Makefile` is the maintained, committed entry point; every invocation regenerates the gitignored `Makefile.coq` from `_CoqProject` via `coq_makefile` and delegates to it. Run `make` from `Code/`.
Single file: `make Classes/StateArrowT/Core.vo`. Use `timeout 30 make ...` to catch typeclass loops.
