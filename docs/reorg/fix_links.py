#!/usr/bin/env python3
"""Repair Markdown links and path mentions after the reorganization.

    python3 docs/reorg/fix_links.py BASE_REV [--check]

For every Markdown file, each relative link is resolved against the file's
location at BASE_REV, mapped through the renames between BASE_REV and the
working tree (plus the SPLITS below), and made relative to the file's current
location.  Mentions of old `Code/`-relative paths in text (e.g. backticked
`Taxonomy/BaseSpecMonads/ASPMonad.v`) are replaced by the new path.
`--check` only reports links whose target does not exist.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SKIP = ("docs/reorg", "docs/reorg-plan.md", "docs/meeting-notes", "Code/Backup", "Code/ITreeExamples")
# A split file maps to the part that keeps its main subject.
SPLITS = {
    "Code/Taxonomy/BaseSpecMonads/WPureMonad.v": "Code/WP/WPure.v",
    "Code/Taxonomy/BaseSpecMonads/SPPredicateTransformers.v": "Code/SP/RawSP.v",
    "Code/Taxonomy/BaseSpecMonads/SPostMonad.v": "Code/SP/SPostMonad.v",
    "Code/Taxonomy/Arrows/GaloisArr.v": "Code/GaloisConnections/GaloisArr.v",
    "Code/Taxonomy/Arrows/SPostArr.v": "Code/SP/SPostArr.v",
    "Code/Taxonomy/BaseSpecMonads/MonadTaxonomy.v": "Code/Taxonomy/MonadTaxonomy.v",
}
DIRS = {
    "Code/Classes": "Code/Lib", "Code/Classes/Tests": "Code/Tests",
    "Code/Classes/OptionArrowT": "Code/Lib/Arrow/OptionArrowT",
    "Code/Classes/StateArrowT": "Code/Lib/Arrow/StateArrowT",
    "Code/Taxonomy/ComputationMonads": "Code/Computation",
    "Code/Taxonomy/BaseSpecMonads": "Code/SP", "Code/Taxonomy/Arrows": "Code/SP",
    "Code/Taxonomy/Arrows/Tests": "Code/Tests", "Code/Taxonomy/Arrows/Examples": "Code/Tests",
    "Code/Taxonomy/Triples": "Code/Triples", "Code/Taxonomy/DijkstraMonads": "Code/Dijkstra",
    "Code/Taxonomy/deprecated": "Code/Backup/Taxonomy-deprecated",
    "Code/Taxonomy/MeetingNotes": "docs/meeting-notes",
    "Code/Taxonomy/README.md": "docs/design.md",
}
LINK = re.compile(r"(\]\()([^)\s#]+)(#[^)]*)?(\))")


def renames(base):
    out = subprocess.run(["git", "diff", "-M50%", "--name-status", base], cwd=REPO,
                         capture_output=True, text=True, check=True).stdout
    m = {}
    for line in out.splitlines():
        p = line.split("\t")
        if p[0].startswith("R"):
            m[p[1]] = p[2]
    m.update(SPLITS)
    return m


def old_location(path, rmap):
    inv = {v: k for k, v in rmap.items() if k not in SPLITS}
    return inv.get(path, path)


def new_target(old_target, rmap):
    if old_target in rmap:
        return rmap[old_target]
    t = old_target.rstrip("/")
    for d in sorted(DIRS, key=len, reverse=True):
        if t == d or t.startswith(d + "/"):
            return DIRS[d] + t[len(d):]
    return old_target


def main():
    base = sys.argv[1]
    check_only = "--check" in sys.argv
    rmap = renames(base)
    code_paths = sorted(((k[5:], v[5:]) for k, v in rmap.items()
                         if k.startswith("Code/") and v.startswith("Code/") and k.endswith(".v")),
                        key=lambda kv: len(kv[0]), reverse=True)
    broken = 0
    for md in sorted(REPO.rglob("*.md")):
        rel = str(md.relative_to(REPO))
        if rel.startswith(SKIP) or "/." in rel:
            continue
        text = md.read_text()
        old_dir = os.path.dirname(old_location(rel, rmap))
        new_dir = os.path.dirname(rel)

        def fix(m):
            target = m.group(2)
            if re.match(r"^[a-z]+:", target):
                return m.group(0)
            old_abs = os.path.normpath(os.path.join(old_dir, target))
            new_abs = new_target(old_abs, rmap)
            if not (REPO / new_abs).exists():
                return m.group(0)
            new_rel = os.path.relpath(new_abs, new_dir)
            return m.group(1) + new_rel + (m.group(3) or "") + m.group(4)

        new = text if check_only else LINK.sub(fix, text)
        if not check_only:
            for old, nw in code_paths:
                new = re.sub(r"(?<![\w/.])(Code/)?" + re.escape(old) + r"\b",
                             lambda mm: (mm.group(1) or "") + nw, new)
        for m in LINK.finditer(new):
            t = m.group(2)
            if not re.match(r"^[a-z]+:", t) and not (REPO / new_dir / t).exists():
                print(f"broken: {rel}: {t}")
                broken += 1
        if new != text:
            md.write_text(new)
    print(f"{broken} broken links")
    sys.exit(1 if broken and check_only else 0)


if __name__ == "__main__":
    main()
