#!/usr/bin/env python3
"""Move the agent context documents into docs/agents/context/ and repair links.

Links inside a moved file are resolved against its old directory; links in
other Markdown files are resolved against their own.  A target that is itself
moved is mapped; then every link is made relative to the file's new place.
Backticked repo-relative mentions of a moved file are rewritten too.
"""
import os
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
D = "docs/agents/context"
MOVES = {"CONTEXT-MAP.md": f"{D}/README.md", "Code/CONTEXT.md": f"{D}/Code.md"}
for d in ["Lib", "Lib/Arrow/OptionArrowT", "Lib/Arrow/StateArrowT", "Computation", "Relational",
          "WP", "SP", "PTMonadTaxonomy", "Triples", "DijkstraMonads", "GaloisConnections",
          "Tests", "Checks"]:
    MOVES[f"Code/{d}/CONTEXT.md"] = f"{D}/{d}.md"
SKIP = ("docs/reorg/", "docs/reorg-plan.md", "docs/meeting-notes", "docs/removed-files.md",
        "Code/Backup", "Code/ITreeExamples")
LINK = re.compile(r"(\]\()([^)\s#]+)(#[^)]*)?(\))")


def relink(text, old_dir, new_dir):
    def fix(m):
        t = m.group(2)
        if re.match(r"^[a-z]+:", t):
            return m.group(0)
        target = os.path.normpath(os.path.join(old_dir, t))
        target = MOVES.get(target, target)
        return m.group(1) + os.path.relpath(target, new_dir) + (m.group(3) or "") + m.group(4)
    text = LINK.sub(fix, text)
    for old, new in MOVES.items():
        text = re.sub(r"`(?:\.\./)*" + re.escape(old) + "`", f"`{new}`", text)
    return text


texts = {}
for md in REPO.rglob("*.md"):
    rel = str(md.relative_to(REPO))
    if rel.startswith(SKIP) or "/." in rel:
        continue
    texts[rel] = md.read_text()
for old, new in MOVES.items():
    (REPO / new).parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "mv", old, new], cwd=REPO, check=True)
for rel, text in texts.items():
    new_rel = MOVES.get(rel, rel)
    out = relink(text, os.path.dirname(rel), os.path.dirname(new_rel))
    if out != text or new_rel != rel:
        (REPO / new_rel).write_text(out)
