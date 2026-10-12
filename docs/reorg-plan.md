# Plan: reorganize the artifact to follow the paper

Status: revised after three reviews (paper fidelity, Coq engineering, artifact
evaluation), then executed on branch `reorganize-by-paper` (worktree
`../artifact-reorg`). See "As executed" at the end.

## Goal

A reader holding the paper (`paper/idm/idm.tex`) opens `Code/`, finds one
directory per paper section in paper order, and goes from any claim to its
Rocq name through `PAPER.md` / `Checks/PaperClaims.v`. Directories form an
acyclic graph whose edges point only backwards in the paper; a script checks
this.

## Ground rules

1. **Moves, splits and file renames only.** No proof, definition or
   identifier changes. Edits inside `.v` files are limited to `Require` /
   `Import` sentences, file header comments, and qualifiers forced by a
   split or rename (`SPPredicateTransformers.X` → `MonotoneSPSt.X`).
2. **Every step is one commit that builds from scratch**: delete all build
   products under `Code/` first (stale `.vo` files silently satisfy a
   missed import rewrite), then `make -j8 && make check`.
3. **Conservation is checked mechanically** at every step:
   - `scripts/inventory.py compare`: same declarations (kind, module path,
     name) with the same statements printed under `Set Printing All`, and the
     same `About` facts (implicit arguments, opacity), file qualifiers
     normalized;
   - the same instance database (`Print HintDb typeclass_instances` from a
     file that requires the whole build, normalized);
   - `make check` prints the same axioms for the same lemmas;
   - for a pure move, the file body with `Require`/`Import` sentences removed
     is byte-identical; for a split, the new bodies are a permutation of the
     old body's top-level blocks plus duplicated preamble lines, which the
     commit message lists.
4. `Require` sentences are rewritten by a script that parses each sentence
   (multi-line lists, bare `Require`, `Export`, mid-file Requires, unrooted
   `From Incorrectness Require …`) and regroups modules by their new
   directory, keeping their order (instances of equal priority are tried in
   load order).
5. The logical root stays `Incorrectness` unless the authors decide
   otherwise (open question 1).

## Layers

`scripts/layers.txt` (checked by `scripts/depgraph.py --check-layers`):

| Layer | Paper | May import |
|---|---|---|
| `Lib/` (`Monad/`, `Arrow/`, `Galois.v`; one layer) | background on demand | — |
| `Computation/` | §1, §5 computation monad | Lib |
| `Relational/` | proof infrastructure, no paper section | Lib |
| `WP/` | §2, §3.6 | Lib |
| `SP/` | §3.1–3.5 | Lib, Relational |
| `Taxonomy/` | §4 | Lib, Relational, WP, SP |
| `Triples/` | §5 (and the §4.1 triple diagram, which needs the morphisms) | Lib, Computation, Relational, WP, SP, Taxonomy |
| `DijkstraMonads/` | §6 | all above |
| `GaloisConnections/` | §7 | Lib, Relational, WP, SP, Taxonomy |
| `Tests/` | — | anything |

`Relational/` sits below `SP/` because `SPostArr.v` proves its laws through
relational readings; `PredMonad.v` lives there because §4, §5 and §7 all use
`Pred`. Both facts are stated in the directory README.

## File mapping

`T/` = `Taxonomy/` today. Splits are at top-level banners; line ranges are
today's.

| Today | After |
|---|---|
| `Classes/{OrderedMonad,MonadRelation}.v`, `T/ComputationMonads/TransformerLaws.v` | `Lib/Monad/` |
| `Classes/Galois.v` | `Lib/Galois.v` |
| `Classes/{Arrow,ArrowApplyFacts,ArrowMonad,ArrowMorphism,RelArrowCoherence,OptionArrowT,StateArrowT}.v` and the two sub-directories | `Lib/Arrow/` |
| `T/ComputationMonads/DivNonDetNE.v` | `Computation/` |
| `T/Arrows/{Rel,RelSPostArr,OptionLoop}.v`, `T/BaseSpecMonads/PredMonad.v` | `Relational/` |
| `T/BaseSpecMonads/SPure.v` | `Relational/RelMonads.v` (renamed: it defines relational `SPSt`/`SPStExc`, not SP transformers) |
| `T/BaseSpecMonads/WPureMonad.v` | `WP/WPure.v` (1–244: `WPure`, `WSt`, `WStExc`, laws, orders) + `WP/WPVariants.v` (245–end: healthiness, `WPSub`, AWP/DWLP/DWP/AWLP) |
| `T/BaseSpecMonads/SPostMonad.v` | `SP/SPostMonad.v` (`SPM`, order, `KenjiPureSP`, `KenjiPureDSLP`; §3.1) + `SP/StatefulSPostCounterexample.v` (`KenjiProgSP`, `KenjiFailingBind`, `StKenji`; §3.3) |
| `T/BaseSpecMonads/SPPredicateTransformers.v` | `SP/RawSP.v` (1–189: `SPPure`, `SPSt`, `SPStExc`, `StTrans`, orders) + `Taxonomy/MonotoneSPSt.v` (190–end: `SPStMonotone`, `lunitStrictlyLax`, `Ladj`/`Radj`, `PredSt`) |
| `T/Arrows/PredicateTransformerProperties.v`, `T/Arrows/SPostArr.v`, `T/Arrows/SPostArrEquiv.v` | `SP/` |
| `T/BaseSpecMonads/{ASP,DSLP,DSP,ASLP}Monad.v` | `SP/` (the pure collapse stays at the end of DSP/ASLP: §6 needs `OrderedMonad_DSP`) |
| `T/Arrows/GaloisArr.v` | `Taxonomy/TransformerTaxonomy.v` (390–end, plus `MonotoneSPost`, `SPost_le` and their preorders from 72–84, 106–115) + `GaloisConnections/GaloisArr.v` (the rest) |
| `T/BaseSpecMonads/{SPStBindComparisons,MonadTaxonomy}.v` | `Taxonomy/` |
| `T/Triples/*.v` | `Triples/` |
| `T/DijkstraMonads/*.v` | `DijkstraMonads/` |
| `T/BaseSpecMonads/{PrePostMonad,RelPrePostMonad,BaseGaloisConnections}.v`, `T/Arrows/{PrePostArr,RelPrePostArr,WPArr}.v` | `GaloisConnections/` |
| `Classes/Tests/*.v`, `T/Arrows/Tests/*.v`, `T/Arrows/Examples/*.v` | `Tests/` |
| `T/deprecated/` | `Backup/Taxonomy-deprecated/` (the hyphen keeps it off the `-Q` load path) |
| `T/MeetingNotes/` | `docs/meeting-notes/` |

Optional splits, after the required steps:

- `SP/SPostArr.v` at line 1787 → keep 1–1786 as `SP/SPostArr.v` (§3.4:
  ASP, DSLP), new `SP/DSPASLPArr.v` (§3.5: DSP, ASLP, separation theorems).
  `DSPMonad`/`ASLPMonad` import it. Not a re-export shim: `Require Export`
  does not alias qualified names.
- `Taxonomy/MonadTaxonomy.v` at line 921 → `Taxonomy/TaxonomyCarriers.v`
  (134–920: the carriers inside `MonoPT`) and `MonadTaxonomy.v` (the
  Figure 1 edges, name kept so the paper's Artifact path stays valid). A finer
  split buys nothing: `Diagram.v` needs `galois_asp_rel`, which depends on
  15 of 18 earlier sections.

## Steps

Each step: one commit; clean build; `make check`; inventory and instance
comparison; layer check (reporting only until step 7, enforcing after).

0. **Tooling and baseline.** `Code/scripts/inventory.py` (declarations,
   statements, `About`, instances); `depgraph.py --check-layers` and a
   directory-only view; `docs/reorg/rewrite_requires.py` (the `Require`
   rewriter, driven by the mapping table above); `docs/reorg/check_links.py`
   (every `*.v` / `*.md` path in Markdown exists); a list of `Admitted` /
   `Abort` in the build. Record baseline outputs.
1. **Clear the names.** Move `T/deprecated/`, `T/MeetingNotes/`.
2. **`Lib/`.**
3. **`Computation/`, `Relational/`** (with the `SPure.v` → `RelMonads.v` rename).
4. **`WP/`, `SP/`, `Taxonomy/`, `Triples/`, `DijkstraMonads/`,
   `GaloisConnections/`, `Tests/`**, unsplit. Interim homes:
   `WP/WPureMonad.v`, `SP/SPPredicateTransformers.v`, `SP/SPostMonad.v`,
   `GaloisConnections/GaloisArr.v`. Afterwards `git status --ignored` shows
   nothing under the old directories.
5. **Split `WPureMonad.v`.**
6. **Split `SPPredicateTransformers.v`.** `RawSP.v` needs only lines 1–5's
   imports; `MonotoneSPSt.v` duplicates `Import MonadNotation. Open Scope
   monad_scope.`
7. **Split `GaloisArr.v`**; point `Diagram.v` and `MonadTaxonomy.v` at
   `TransformerTaxonomy`. Turn on the layer check.
8. **Split `SPostMonad.v`.**
9. **(Optional) the two splits above.**
10. **`Checks/PaperClaims.v` and `PAPER.md`.** `PaperClaims.v` is compiled by
    `make check`; for each paper section and contribution it `Check`s the
    claimed results. `PAPER.md` has one table per section: paper text |
    Rocq name | file | status (proved / partial / not mechanized). A script
    checks that every name in `PAPER.md` is in the inventory.
    It must state the gaps the reviews found:
    - §7 lifted Galois connections (intro bullet 6) are not formalized; the
      §4 monadic-relation lifting of `GaloisPredWP` is the nearest result;
      `NewGaloisConnections.v` does not exist (`wp_pp_over_adjunction` is in
      `BaseGaloisConnections.v`);
    - no Pred ≅ SPost/ASP/DSLP isomorphism; nearest: `asp_to_rel_morphism`,
      `asp_to_dslp`, `Galois_Rel_SPost`;
    - the WP morphisms land in `WPure`; no lemma puts them in DWP, AWP, …;
    - §3.3: only the angelic counterexample, and for a hand-built
      `KenjiProgSP`, not literally `stateArrT` over `SPostArr_ang`;
    - SPost_dem is `DSLPSP`; ASP ≅ SPost_ang goes through
      `kenji_iff_singleton` and `aspsp_to_asp`;
    - §3.4's stateful "codomain ⇔ strict" is proved only without state;
    - §4.3 has no code;
    - `Radj_bind` is `Admitted` (open question 3);
    - beyond the paper: `OptionLoop.v`, `InCorrectnessPrinciples.v`,
      `GaloisConnections/GaloisArr.v`, `SPStBindComparisons.v`.
11. **Docs.** One README per directory (paper section, files, reading order,
    exceptions), assembled from today's `CONTEXT.md` files; the 942-line
    `Taxonomy/README.md` reordered into paper order as `Code/README.md`, its
    development-only sections moved to `docs/design.md`; evaluator section
    of the top `README.md` (versions, build time, axioms, where to start);
    `CONTEXT-MAP.md`, `CLAUDE.md` paths; link check passes; regenerate
    `depgraph.html`; the layer check as its own CI step.

## Open questions for the authors

1. Rename the logical root `Incorrectness` (e.g. `PTMonads`)? Free during
   step 2, costly later.
2. Remove `Backup/`, `ITreeExamples/`, agent docs from the submitted
   artifact (build it with `git archive` from an allowlist), or keep them?
3. `Radj_bind` (`Admitted`, unused): finish, delete, or disclose?
4. Add a `LICENSE` file (the opam file says MIT)?

## Out of scope

- Merging the three definitions of strict/terminating/conjunctive/disjunctive.
- Updating the "Artifact:" paths inside `idm.tex` (separate repository);
  `PAPER.md` gives the new paths.

## As executed

Every code step is one commit (step 4: one per destination directory),
verified from a clean build with `docs/reorg/verify.sh`: same declarations,
statements (`Set Printing All`), `About` facts, distinct instances and
`make check` assumptions as the baseline; layer check; renamed bodies
unchanged apart from Requires (or comments only, reported as such); for each
split, `split.py --check` (the parts' code is the old code plus the listed
duplicated preamble lines).

| Step | Commits |
|---|---|
| 0 tooling | `76ab804` |
| 1 clear names | `fbe53d4` |
| 2 Lib | `993d5d0` |
| 3 Computation, Relational | `a0b37cc` |
| 4 moves | `257b981` `5fb9848` `66ee0e5` `c863a4c` `bf80471` `d3c7b3f` `4ba2d1f` `474bda8` |
| 5 WPure / WPVariants | `97d7eeb` |
| 6 RawSP / MonotoneSPSt | `c1381f7` |
| 7 TransformerTaxonomy / GaloisArr, layers enforced | `c10e640` |
| 8 StatefulSPostCounterexample | `446c99b` |
| optional: SPostArr / DSPASLPArr | `e433f07` |
| optional: TaxonomyCarriers / MonadTaxonomy | `dbc9817` |
| docs | `f944b79` `b7fefda` `328988a`, then the claims index |

Departures from the plan:

- After the final review, the section 4 directory `Taxonomy/` was renamed
  `MonadRelations/` (the paper uses "taxonomy" for the whole paper, for
  section 4.1's taxonomy of triples, and for Figure 1): `TransformerTaxonomy.v`
  -> `TransformerRelations.v`, `TaxonomyCarriers.v` -> `Carriers.v`, and
  `Triples/Diagram.v` -> `Triples/TripleTaxonomy.v`. `MonadTaxonomy.v` keeps
  its name (Figure 1; cited by the paper). The directory was then renamed
  again, `MonadRelations/` -> `PTMonadTaxonomy/`, to match Section 4's title
  without clashing with the paper title or with `Lib/Monad/MonadRelation.v`.
  `Dijkstra/` was renamed `DijkstraMonads/` likewise. `Computation/`, `Triples/` and
  `DijkstraMonads/` were then grouped under `Verification/`, and the context
  guides moved to `docs/agents/context/`. Last, `Verification/Triples/MonadMorphisms.v`
  was split: the 24 morphisms, shared by triples and Dijkstra monads, went to
  `Verification/MonadMorphisms/MonadMorphisms.v`; their 46 triple lemmas
  stayed as `Verification/Triples/MorphismTriples.v` (`specs/step11_morphisms.py`).
  Then `DijkstraMonad.v` was split at its comparison with triples
  (`specs/step12_typings.py`): the construction stays in
  `Verification/DijkstraMonads/`, which no longer depends on `Triples/`; the
  comparison and `DijkstraExamples.v` went to `Verification/TriplesAsTypings/`.
  Finally `Verification/` was split by setting (`specs/step13_settings.py`,
  `partition.py`, checked by `partition_check.py`): `Generic/` (the same at
  every setting), `Base/` (`divndNE`), `State/` and `StateExc/` (its two
  lifts, siblings). Every declaration went to the highest setting its code
  or its dependencies name; sections serving several settings were cut with
  their headers copied; 379 qualified names follow
  (`docs/reorg/partition-map.txt`). The setting directories were then renamed `DivNonDet/`,
  `DivNonDetSt/`, `DivNonDetStExc/`, with the same file names in each
  (`Computation.v`, `Morphisms.v`, `Triples.v`, `TriplesTaxonomy.v`,
  `DijkstraMonads.v`, `Typings.v`). Afterwards every Verification file's project imports were
  minimized (`minimize_requires.py`: an import is dropped when the file still
  compiles without it, then the whole build is redone), and the four
  `SpecReading` instances of the base SP monads, which the partition had put
  in `Generic/Triple.v` (its keyword list missed the bare monad names), moved
  to `DivNonDet/Triples.v`.
- New code (not a move): O'Hearn's rewriting rules, previously only with
  state, were proved once in `Generic/InCorrectnessPrinciples.v` for the ASP
  reading of any relation and instantiated in every setting
  (`DivNonDet/`, `DivNonDetStExc/` new; the state rules re-derived with
  identical statements), with the base Galois edge
  `dwlp_under_galois_asp_over_pure`. 41 declarations were added, none removed
  or changed; all are closed under the global context. The plan above uses
  the earlier names.

- Docs keep the repository's `CONTEXT.md` convention (one per directory)
  instead of per-directory READMEs; `Code/README.md` is the entry point and
  the old `Taxonomy/README.md` became `docs/design.md`.
- The layer check is not part of `make check`, which runs inside the Coq
  container in CI: it is `make layers` and a separate CI job, with a
  Require-parsing fallback when `coqdep` is absent (same edges as `coqdep`).
- Instance database: after the `SPostArr.v` split the 24 DSP/ASLP instances
  are registered once instead of twice. The second copy came from the alias
  `Module PropertySP := SPostArr.` in `SPostArrEquiv.v`, which does not cover
  `DSPASLPArr.v`. Distinct instances are unchanged.
- One elaborated term changed (found by the final engineering review, which
  compared the `Print` of all 2927 declarations at the base and at the head):
  the transparent instance `GaloisArr.Galois_Rel_SPost` now fills its
  `PreOrder` field with `TransformerTaxonomy.pt_le_PreOrder` instead of
  `MonotoneSPost_le_PreOrder`. Step 7 made `pt_le_PreOrder` visible earlier
  in `GaloisArr.v`, and it wins resolution. Both are `Prop` proofs about
  definitionally equal relations, so nothing downstream changes; sources are
  otherwise unchanged and 2907 declarations are identical, the other 19
  differing only in auto-generated names.
- Known blind spots of the per-step checks: `inventory.py` compares types,
  not bodies; its qualifier normalization merges same-named declarations of
  different files (`SPSt` in RawSP / RelMonads, `retP` in WPure /
  PredMonad, ...); notations are compared by name; the instance database is
  the one seen by a file requiring the whole build. The final review covered
  the first two with a strict body comparison.
- Split importers: SP files may only import `RawSP.v`; files that imported a
  whole split file outside SP keep importing every part they use.
- Merged `main` at `8e2fccb` (six arrow-law commits: core `pure_proper`,
  transformer lift laws, `PureProperRegression.v`). New files went to
  `Lib/Arrow/{OptionArrowT,StateArrowT}/TransformerLaws.v` and `Tests/`;
  their context edits to `Tests.md`, `Lib.md` and `Lib/Arrow/*.md`. Checked
  against `8e2fccb` as for the steps: same assumption reports (plus the
  branch's 27 extra, all closed), the same 41 additions and nothing else, and
  every renamed file with `main`'s body. `inventory.py` now skips
  `Fail Definition` names, which the `.glob` records.

Directory graph after the reorganization (transitively reduced; was 6
directories with an `Arrows` <-> `BaseSpecMonads` cycle): see
[Code/README.md](../Code/README.md#layout-in-paper-order).
