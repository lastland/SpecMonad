#!/usr/bin/env python3
"""Check a partition: the targets' code (comments and Requires removed) is the
sources' code at REV, up to copies of section open/close lines, section
preambles and shared commands, and the qualified-name rewrites listed in
docs/reorg/partition-map.txt.

    python3 docs/reorg/partition_check.py SPEC.py REV [RENAMES.txt]
"""
import re
import runpy
import subprocess
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from partition import units, CODE  # noqa: E402
from split import code_lines  # noqa: E402

spec = runpy.run_path(sys.argv[1]); rev = sys.argv[2]
REPO = CODE.parent
moved = {}
for line in (REPO / "docs/reorg/partition-map.txt").read_text().splitlines():
    a, b = line.split(" -> ")
    moved[b] = a        # new qualified -> old qualified
if len(sys.argv) > 3:   # names whose file was renamed again later
    stems = {Path(l.split("=")[0]).stem: Path(l.split("=")[1]).stem
             for l in Path(sys.argv[3]).read_text().split()}
    for b, a in list(moved.items()):
        st, nm = b.split(".", 1)
        if st in stems:
            moved[f"{stems[st]}.{nm}"] = a
    # names that stayed in their file during the partition, renamed with it
    for l in Path(sys.argv[3]).read_text().split():
        o, nw = l.split("=")
        for nm in re.findall(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Program\s+)?(?:Theorem|Lemma|Definition|"
                             r"Corollary|Instance|Fixpoint|Example|Inductive|Record|Class)\s+([\w']+)",
                             (CODE / nw).read_text(), re.M):
            moved.setdefault(f"{Path(nw).stem}.{nm}", f"{Path(o).stem}.{nm}")
qual = re.compile(r"(?<![\w.'])([A-Za-z_][\w']*\.[A-Za-z_][\w']*)")
undo = lambda t: qual.sub(lambda m: moved.get(m.group(1), m.group(1)), t)
old, dup_ok = Counter(), Counter()
for s in spec["SOURCES"]:
    text = subprocess.run(["git", "show", f"{rev}:Code/{s}"], cwd=REPO, capture_output=True,
                          text=True, check=True).stdout
    old += Counter(code_lines(text))
    _, us, _ = units(text)
    for u in us:
        if u[2] in ("section-open", "section-close", "preamble", "shared"):
            for l in code_lines(u[1]):
                dup_ok[l] += 30   # may be copied into several targets
# Later renames of the targets (old=new per line), if given.
ren = dict(l.split("=") for l in Path(sys.argv[3]).read_text().split()) if len(sys.argv) > 3 else {}
targets = sorted({ren.get(t, t) for t in spec["TARGET"].values() if t})
new = Counter()
for t in targets:
    new += Counter(code_lines(undo((CODE / t).read_text())))
missing, extra = old - new, new - old
bad = extra - dup_ok
for l in missing.elements():
    print("missing:", l)
for l in bad.elements():
    print("unexpected:", l)
print(f"partition check: {sum(old.values())} source code lines, {sum(extra.values())} copied "
      f"(section headers, preambles, shared), {'OK' if not missing and not bad else 'FAILED'}")
sys.exit(0 if not missing and not bad else 1)
