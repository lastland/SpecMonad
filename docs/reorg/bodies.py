#!/usr/bin/env python3
"""For every file renamed between BASE and the working tree, check that its
body is unchanged once Require sentences are removed.  A change confined to
comments is reported as such; any other change fails.

    python3 docs/reorg/bodies.py BASE_REV
"""
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from move import SENTENCE  # noqa: E402

REPO = Path(__file__).resolve().parents[2]


def body(text):
    return [l for l in SENTENCE.sub("", text).splitlines() if l.strip()]


def code(text):
    # Coq comments nest; strip innermost first.
    prev = None
    while prev != text:
        prev, text = text, re.sub(r"\(\*(?:(?!\(\*).)*?\*\)", " ", text, flags=re.S)
    return " ".join(SENTENCE.sub("", text).split())


base = sys.argv[1]
out = subprocess.run(["git", "diff", "-M50%", "--name-status", base, "--", "Code"],
                     cwd=REPO, capture_output=True, text=True, check=True).stdout
bad = 0
for line in out.splitlines():
    parts = line.split("\t")
    if not parts[0].startswith("R") or not parts[1].endswith(".v"):
        continue
    old = subprocess.run(["git", "show", f"{base}:{parts[1]}"], cwd=REPO,
                         capture_output=True, text=True, check=True).stdout
    new = (REPO / parts[2]).read_text()
    if body(old) == body(new):
        verdict = "same"
    elif code(old) == code(new):
        verdict = "comments only"
    else:
        verdict = "BODY CHANGED"
        bad += 1
    print(f"{verdict}  {parts[1]} -> {parts[2]}")
sys.exit(1 if bad else 0)
