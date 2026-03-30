# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Meta rules for this file

- Do NOT add anything easily inferred by Claude Code (file structure, build commands, standard Coq patterns).
- Do NOT add common Coq knowledge.
- Refer to existing docs (`README.md` for project goals/status, `Code/coq-spec-monad.opam` for dependencies) instead of repeating their content.
- If something project-specific warrants a reusable skill, ask the user rather than bloating this file.

## Development rules

- Always look up ITree and ExtLib libraries first before defining something new, to avoid reinventing the wheel.
- Prefer `#[program] Definition` over `refine` for subset types; keep tactics for proof obligations only.

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
