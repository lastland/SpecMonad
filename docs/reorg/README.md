# Reorganization scripts

These scripts moved the Coq sources into the paper-ordered layout of `Code/`
(2026-10, merged into `main` at `32294ed`). They also checked that nothing was
lost or changed on the way. The step-by-step plan and its execution log were
removed afterwards; read them with
`git show 32294ed:docs/reorg-plan.md`. The commit messages (`Reorg step N`
and the commits after them up to `32294ed`) record what each step did and how
it was checked.

Run everything from the repository root unless noted. Paths given to the
scripts are relative to `Code/`.

## Reusable: moving and checking

| Script | Use |
|---|---|
| `move.py OLD.v=NEW.v ...` | `git mv` Coq files, update `_CoqProject`, and rewrite every `Require` that names them. Sentences that name no moved module stay byte-identical. |
| `split.py SPEC.py` | Split one file into several by line ranges, and rewrite its importers' `Require`s. `split.py SPEC.py --check REV` checks that the parts' code is the source's at `REV`, plus only the lines listed in `DUPLICATED`. The specs in `specs/stepN_*.py` are worked examples. |
| `minimize_requires.py FILE.v ...` | Drop project imports a file compiles without. Rebuild from scratch afterwards: a downstream file may have relied on an instance loaded on its behalf. |
| `bodies.py BASE_REV` | For every file renamed since `BASE_REV`, check that its body is unchanged once `Require`s are removed. A change confined to comments is reported as such; any other change fails. |
| `fix_links.py BASE_REV [--check]` | Repair Markdown links and backticked `Code/` paths after moves. `--check` only reports broken links, and is the one to run after any doc edit. |
| `verify.sh BASELINE_DIR [BASE_REV]` | Full check of a refactoring, see below. |

Two tools from `Code/scripts/` do the heavy lifting:

- `inventory.py snapshot OUT.json` prints the statement of every declaration
  of the build and the instance database (run from `Code/`, after `make`).
  `inventory.py compare OLD.json NEW.json` matches declarations by name and
  module path, ignoring which file they live in. It reports declarations
  added or removed, statements changed, and instance differences.
- `depgraph.py` writes the dependency graph (`depgraph.html`).
  `--check-layers` checks the import layering of `scripts/layers.txt`; this is
  what `make layers` and CI run. `--mermaid` prints the directory graph.

### Checking a refactoring against a baseline

To verify that a change (a move, a split, a merge) keeps every declaration and
assumption, snapshot the baseline revision in a scratch worktree, then run
`verify.sh` on the working tree:

```sh
B=/path/to/scratch
git worktree add --detach $B/base main          # the revision to compare against
cd $B/base/Code && make -j8 \
  && make check 2>&1 | grep -vE '^(make|COQ|coq_makefile|rm )|PaperClaims' > $B/check.log \
  && python3 scripts/inventory.py snapshot $B/inv.json
cd - && docs/reorg/verify.sh $B main
git worktree remove --force $B/base
```

`verify.sh` builds from clean (deleting stale `.vo` files, which would
satisfy a `Require` that still names an old path), then compares the
`make check` assumption reports and the inventory, and checks the layers.
With `BASE_REV`, it also runs `bodies.py`. It stops at the first
difference. When a difference is expected (new lemmas, new
`Print Assumptions` lines), run the later steps by hand and read the
reports.

Known limits: `inventory.py` compares statements, not proofs. Its qualifier
normalization merges same-named declarations of different files, and it
compares notations by name only. `bodies.py` covers renames, not splits;
use `split.py --check` or `partition_check.py` for those.

## One-off: kept as a record

These encode this particular reorganization and would need editing to reuse.

- `partition.py SPEC.py [--dry-run]` split the verification files by setting
  (generic / `DivNonDet` / `DivNonDetSt` / `DivNonDetStExc`). It works one
  command at a time, places each at the lowest setting its code and
  dependencies allow, and rewrites qualified names (`partition-map.txt`
  lists the 379 rewrites). `partition_check.py SPEC.py REV [RENAMES.txt]`
  checks the result; `specs/step13_settings.py` is the spec, and
  `specs/step14_setting_renames.txt` gives the later directory renames.
- `move_contexts.py` and `relink.py` moved the `CONTEXT.md` guides to
  `docs/agents/context/` and repaired their links.
- `fix_links.py` has the splits of this reorganization hard-coded (`SPLITS`),
  and the skip lists of several scripts name the deleted
  `docs/reorg-plan.md`. Both are harmless.
