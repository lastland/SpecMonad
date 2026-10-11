#!/usr/bin/env python3
"""Group Computation/, Triples/ and DijkstraMonads/ under Code/Verification/:
move their context guides to docs/agents/context/Verification/ and repair
Markdown links (resolved against each file's location before the move,
mapped through PREFIX, then made relative to its new location)."""
import os
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
C = "docs/agents/context"
PREFIX = {f"Code/{d}": f"Code/Verification/{d}" for d in ("Computation", "Triples", "DijkstraMonads")}
PREFIX.update({f"{C}/{d}.md": f"{C}/Verification/{d}.md" for d in ("Computation", "Triples", "DijkstraMonads")})
SKIP = ("docs/reorg/", "docs/reorg-plan.md", "docs/meeting-notes", "docs/removed-files.md",
        "Code/Backup", "Code/ITreeExamples")
LINK = re.compile(r"(\]\()([^)\s#]+)(#[^)]*)?(\))")


def mapped(path):
    for old in sorted(PREFIX, key=len, reverse=True):
        if path == old or path.startswith(old + "/"):
            return PREFIX[old] + path[len(old):]
    return path


texts = {str(md.relative_to(REPO)): md.read_text() for md in REPO.rglob("*.md")
         if not str(md.relative_to(REPO)).startswith(SKIP) and "/." not in str(md.relative_to(REPO))}
for old, new in PREFIX.items():
    if old.endswith(".md"):
        (REPO / new).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", old, new], cwd=REPO, check=True)
for rel, text in texts.items():
    new_rel = mapped(rel)
    def fix(m):
        t = m.group(2)
        if re.match(r"^[a-z]+:", t):
            return m.group(0)
        target = mapped(os.path.normpath(os.path.join(os.path.dirname(rel), t)))
        return m.group(1) + os.path.relpath(target, os.path.dirname(new_rel)) + (m.group(3) or "") + m.group(4)
    out = LINK.sub(fix, text)
    if out != text or new_rel != rel:
        (REPO / new_rel).write_text(out)
