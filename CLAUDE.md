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
  - **CoqHammer in proof bodies**: Always use `sauto limit: 200` (not bare `sauto`) — bare `sauto` loops on typeclass-heavy goals. Works well for propositional tails after manual preprocessing (`unfold`/`cbn`/`destruct`). Keep manual proofs for witness construction (pair/sum `exists`), `rewrite` with `IsASP_rewrite`/`IsDSLP_rewrite`, `Proper_bind` setoid reasoning, and typeclass-derived `reflexivity`/`transitivity`. No global limit option exists — limits are per-tactic only.
- **Sort inference in match bodies**: A bare `forall r, ... -> post r` as the body of a `match` against `mkOptionT` / `mkSPRecord` has its sort inferred as `Type`, not `Prop`, breaking `optionT WPure` / `Pred` unification with a confusing universe error. Wrap in a connective (`/\`, `\/`, `exists`) or add a `(_ : Prop)` cast.
- **Classical `itree void1` termination**: Reasoning that a deterministic ITree either converges or diverges requires `eutt_reta_or_div`, `ret_not_div`, `any_infinite_proper_eutt` from `ITree.Extra.Dijkstra.PureITreeBasics` — *not* in the default `From ITree Require Import ITree Eq Props.Infinite.`. `ret_not_div` takes `A` and `E` implicit, so call it as `ret_not_div Hinf`, not `ret_not_div _ _ _ Hinf`.

## Architecture: Classes/

`Code/Classes/` defines Hughes-style arrow typeclasses and generic transformer laws:

- `Arrow.v`: Core typeclasses (`Arrow`, `ArrowChoice`, `ArrowApply`, `ArrowLoop`) + laws + `Pred` (relational arrow, `A -> B -> Prop`) instances.
- `OptionArrowT/`: Generic `optionArrT arr A B := arr A (option B)` transformer. Split into `Core.v`, `ArrowLaws.v`, `ArrowChoiceLaws.v`, `ArrowApplyLaws.v`. `OptionArrowT.v` is a thin re-export. Concrete `optionPred` instances now live in `Taxonomy/Arrows/PredArr.v`.
- `StateArrowT/`: Generic `stateArrT S arr A B := arr (A*S) (B*S)` transformer. Split into `Core.v`, `ArrowChoiceLaws.v`, `ArrowApplyLaws.v`. `StateArrowT.v` is a thin re-export.

All generic law proofs are purely algebraic — they derive from base arrow laws without inspecting the concrete arrow type.

## Architecture: Taxonomy/

The `Code/Taxonomy/` directory is the core of the project. All monads share the shape `stateT S (optionT <base>)`, varying only in the base monad:

| Base monad | Composed type | File | Role |
|---|---|---|---|
| `itree void1` | `stdivitree` | `ComputationMonads/StDivITree.v` | Deterministic computation |
| `WPure` = `(A -> Prop) -> Prop` | `WStExc` | `BaseSpecMonads/WPure.v` | Weakest precondition spec |
| `SetM` = `A -> Prop` | `stexcnd` | `ComputationMonads/StExcNonDet.v` | Nondeterministic computation |
| `optionT SetM` (double optionT) | `stdivexcnd` | `ComputationMonads/StDivExcNonDet.v` | Nondeterminism + divergence |

`SPostArr.v` defines strongest postcondition *arrows* (`PureASPostArr`, `PureDSLPostArr`) using `SPRecord` over `Pred` relations. Composed types: `ASPostArr S A = stateArrT S (optionArrT PureASPostArr) unit A`. `PredArr.v` adds the complementary monad view (`fun B => Pred A B` is a monad for each fixed `A`) plus `optionPred` instances and composed spec-type aliases.

**Observation functions** bridge computation monads to specification types (both WP and SP):
- `EffectObservations/Observation.v`: maps `stdivitree` to 4 SP variants (`obsASP` / `obsDSLP` / `obsDSP` / `obsASLP`) and 4 WP variants (`obsAWP` / `obsDWP` / `obsAWLP` / `obsDWLP`), with `obsWPCollapse` / `obsWLPCollapse` showing angelic-demonic collapse under determinism
- `EffectObservations/NonDetObservation.v`: maps `stexcnd` to `ASPostArr` (SP) and `WStExc` (demonic/angelic WP)
- `NonDetItObservation.v`: maps `stdivexcnd` to `ASPostArr` (SP) and `WStExc` (4 WP variants)

The tail of `NonDetItObservation.v` defines two forward duals of `WPure`/`WStExc`, both `stateT S (optionT _)` with `MonadLawsE` chained through `ComputationMonads/ProgFacts.v`:

| Base | Closed form | Representation | Reading over initial states | Observation |
|---|---|---|---|---|
| `SPPure A = { t : Prop -> A -> Prop \| AdditiveSP t }` | `t p a <-> p /\ t True a` | set (`ofSet`/`spSet`) | join, `readSP` | `SPMonadObs.obsASP` |
| `PureSPM A = { t : Prop -> A -> Prop \| MultiplicativeSP t }` | `t p a <-> p \/ t False a` | co-set (`ofCoSet`/`spCoSet`) | meet, `readSPM` | `SPMonadObs.obsDSLP` |

Additivity/multiplicativity is what makes forward transformers a monad at all — `bind_ret_l` is exactly the closed-form equation. `bindSP` is existential (`exists a, m p a /\ k a True b`), `bindSPM` is its dual nesting (`forall a, m (k a p b) a`). The multiplicative side needs `Classical_Prop.classic`; the additive side is constructive. Both observations are monad morphisms (`obsASPmorph_ret/bind`, `obsDSLPmorph_ret/bind`).

`obsDSP` and `obsASLP` fit **neither** monad, in either assignment — proved, not assumed. They preserve *binary* meets/joins (`obsDSP_meet2`, `obsASLP_join2`) but fail the *empty* ones: `obsDSP` is not top-preserving and `obsASLP` is not strict, at an unreachable outcome (`obsDSP_not_top`, `obsASLP_not_strict`); the swapped assignment fails on binary joins/meets (`obsDSP_not_join2`, `obsASLP_not_meet2`). Four no-go corollaries: `no_ProgSPM_for_obsDSP`, `no_ProgSP_for_obsASLP`, `no_ProgSP_for_obsDSP`, `no_ProgSPM_for_obsASLP`. What does work is the product monad `ProgSPB S A = SPStExc S A * ProgSPM S A` (`SPMonadObsB`), read by meet for DSP and join for ASLP — matching `SPostArr.v`'s `dsp_asp_dslp` / `aslp_asp_dslp`.

An earlier single-observation presentation is also kept: `obsSP` into `SPStExc` with all four SP transformers as readings (`spASP`/`spDSLP`/`spDSP`/`spASLP`, `obsASP_spASP` &c.), plus `tripleSPm` and the transported taxonomy. Prefer `SPMonadObs` when you want the observations to be independent monad-valued maps rather than readings of one reachability object.

**Facts files** (`*Facts.v`) prove laws. `ComputationMonads/ProgFacts.v` provides generic `optionT`/`stateT` monad law instances. `SPostArrFacts.v` proves `ArrowLaws` for the SP arrows.

`WPArr.v` defines the reader-WP Kleisli arrow `WPArr A B := A -> WPure B`; laws in `WPArrFacts.v` hold definitionally (all `reflexivity`). `RelPrePostArr.v` defines `RelPrePost A B := (A -> Prop) -> (A -> B -> Prop) -> Prop` — a "validator" of Hoare specs that embeds `WPArr` injectively. `GaloisArr.v` establishes Galois connections (via Dijkstra refinement order) among `Pred`, `PrePost`, `WPArr`, and `RelPrePost`.

`Taxonomy/deprecated/` holds earlier iterations that are deliberately excluded from `_CoqProject`; ignore them when grepping for symbol references.

## CI

See `.github/workflows/SpecMonad.yml` (Coq 8.20, docker-coq-action via opam).

## Build

`Makefile` is gitignored; regenerate with `coq_makefile -f _CoqProject -o Makefile` in `Code/`.
Single file: `make Classes/StateArrowT/Core.vo`. Use `timeout 30 make ...` to catch typeclass loops.
