# Removed effect-example files

On 2026-10-11 the earlier per-effect developments were removed from `Code/`
and `_CoqProject`. Nothing in the remaining build depended on them. They are
still available on the **`main-backup`** branch (also `origin/main-backup`),
which contains every file listed below unchanged.

```sh
git show main-backup:Code/ST/Pred.v                 # read one file
git ls-tree -r --name-only main-backup Code/Common  # list a directory
git checkout main-backup -- Code/ST Code/Common.v   # restore into the tree
```

A restored file must also be added back to `Code/_CoqProject`. `ST/*` needs
`Common.v` and the five `Common/*` modules it re-exports. Some files in
`Code/Backup/` (outside the build) still import these modules.

Each removed directory also had a `CONTEXT.md` with more detail; read those on
`main-backup` before relying on the summaries below.

## Common — earlier specification-order API

Separate from the generic arrow `Classes/` and the Taxonomy carriers.
`Code/Common.v` (6 lines) re-exported only Notations, Classes,
PureSpecMonads, StateSpecMonads and OptionSpecMonads.

| File | Lines | Contents |
|---|---|---|
| `Notations.v` | 3 | `f ∘ g` notation for `compose`. |
| `Classes.v` | 134 | `PreT`/`PostT`/`PrePostT`, `PredMonad`, `GaloisPrePostPred`. `eqPred` is mutual order; `PredMonadLaws` gives preorder/equivalence, not monad equations. |
| `PureSpecMonads.v` | 245 | `PurePre := Prop`, unary `PurePred`, monotone `SPost` whose output implies the precondition. `pp2p (P,Q) = fun r => P -> Q r`; post-order conditional on the target precondition. |
| `PurePrePostStandard.v` | 253 | Variant of the above comparing posts unconditionally and using `Q` alone. |
| `PureSpecKleisli.v` | 480 | Exploratory: Kleisli presentation, inhabited preconditions, `dualPrePost`. Contains TODOs and aborted/admitted proofs. |
| `StateSpecMonads.v` | 94 | State relations indexed by initial state / result / final state; bind composes existentially; `pp2p` guards the post with the initial precondition. |
| `OptionSpecMonads.v` | 197 | Continues only from `Some`; does not propagate an incoming `None` (unlike `OptionArrowT`). |
| `NonDetSpecMonads.v` | 277 | Predicates on predicates, `(A -> Prop) -> Prop`. |
| `Guarded.v` | 70 | `guarded A = { P : Prop & P -> A }`; `obsPred` universal over guard proofs. |
| `IOStateExc.v` | 212 | Relational `M` vs universal `W` vs existential `WP` for state + exceptions. Outcomes `A * S + E` (note: sum tags reversed relative to STEx); exceptions carry no final state, handlers use the initial state. |

## Identity — pure correctness/incorrectness

| File | Lines | Contents |
|---|---|---|
| `Identity/Identity.v` | 62 | `SPost` maps a propositional precondition to a result predicate implying it (no monotonicity); `theta m := SPost_ret m`; `Incorrect` requires `achieves r -> r = m /\ presumes`. Final example ends in `Abort`. Uses CoqHammer. |
| `Identity/IdentityVariations.v` | 297 | Three modules: `ContextFree` (`exists γ, m γ = r /\ P γ`), `ContextFull` (`m γ = r /\ P γ`), `ContextImplicit` (`m = r /\ P`). `Incorrect`/`Correct`, weakening, disjunction, monotonicity and agreement lemmas with module-specific quantifiers. Source spelling `Incorect` is intentional. |

## Reader — environment-indexed specifications

| File | Lines | Contents |
|---|---|---|
| `Reader/Reader.v` | 418 | `Reader` spec (result predicate per environment and pre, implying pre), `WFReader` adds monotonicity. ret/bind/ask/local instances; monad laws unproved. `obsReader m s0 pre r = runReader m s0 = r /\ pre`; `Verify` = spec implies observation (opposite to ST). `WithStateFreeAchieves` vs `WithStateAwareAchieves` SP variants, Incorrect/Correct, agreement, `example_3_1r/R`. Uses ExtLib and CoqHammer. |

## ST — state via `Common` relations

| File | Lines | Contents |
|---|---|---|
| `ST/Pred.v` | 310 | Observes `runState m s0 = (r,s1)`; `Verify` is `ordPred (obs m) w` (opposite to Reader/STEx). `Correct` via `pp2p`, `Correct'` via `ordPrePost`. `Incorrect` requires an initial-state witness per asserted result/final-state pair. Rule modules with agreement; `OHearnExample` final proof aborted. |
| `ST/GuardedPred.v` | 160 | `S -> guarded (S * A)`. `obsPredForall` (universal over guard proofs, may hold vacuously) for `Correct`; `obsPredExists` + `VerifyIncorrect` for `Incorrect`. |

Both imported `Common.v`, ExtLib and CoqHammer.

## STEx — state and exceptions

| File | Lines | Contents |
|---|---|---|
| `STEx/Examples.v` | 14 | Deterministic state/exception programs in ExtLib `stateT`, e.g. `read_if_inc_write`. |
| `STEx/STEx.v` | 229 | Spec over `E + A * S` (exceptions `inl`, no final state). ret/bind/get/put/raise/catch; monad laws unproved; catch runs the handler at the original state. `obsSTEx`, `Verify` (spec implies observation); no catch verification theorem. `Incorrect`, `IncorrectNormal`/`Err`, `Incorrect'`. `ReadIfIncWrite` example (increment if initial state ≥ 42, else exception). Uses ExtLib and CoqHammer. |
