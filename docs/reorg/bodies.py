#!/usr/bin/env python3
"""For every file renamed between BASE and the working tree, check that its
body is unchanged once Require sentences are removed.  A change confined to
comments is reported as such; any other change fails.

    python3 docs/reorg/bodies.py BASE_REV
"""
import re
import runpy
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
# Split files are checked by `split.py --check`, not here.
SPECS = [runpy.run_path(str(f)) for f in sorted((Path(__file__).parent / "specs").glob("*.py"))]
# Renames made after the splits (section 4 directory named by content).
LATER = {"Code/Taxonomy/TransformerTaxonomy.v": "Code/MonadRelations/TransformerRelations.v",
         "Code/Taxonomy/TaxonomyCarriers.v": "Code/MonadRelations/Carriers.v",
         "Code/Taxonomy/MonotoneSPSt.v": "Code/MonadRelations/MonotoneSPSt.v",
         "Code/Taxonomy/MonadTaxonomy.v": "Code/MonadRelations/MonadTaxonomy.v",
         "Code/Taxonomy/SPStBindComparisons.v": "Code/MonadRelations/SPStBindComparisons.v",
         "Code/Triples/Diagram.v": "Code/Triples/TripleTaxonomy.v"}
LATER_QUALIFIERS = [("TransformerTaxonomy", "TransformerRelations"),
                    ("TaxonomyCarriers", "Carriers"), ("Diagram", "TripleTaxonomy")]
SPLIT_FILES = {"Code/" + p for sp in SPECS for p in [sp["SOURCE"]] + [x[0] for x in sp["PARTS"]]}
SPLIT_FILES |= {LATER[f] for f in SPLIT_FILES if f in LATER}
# Qualifier rewrites a split forced on other files, applied to the old text.
QUALIFIED = {}
for sp in SPECS:
    for f, pairs in sp.get("QUALIFIED", {}).items():
        QUALIFIED.setdefault("Code/" + f, []).extend(pairs)
out = subprocess.run(["git", "diff", "-M50%", "--name-status", base, "--", "Code"],
                     cwd=REPO, capture_output=True, text=True, check=True).stdout
bad = 0
for line in out.splitlines():
    parts = line.split("\t")
    if not parts[0].startswith("R") or not parts[1].endswith(".v"):
        continue
    if parts[1] in SPLIT_FILES or parts[2] in SPLIT_FILES:
        print(f"split (see split.py --check)  {parts[1]} -> {parts[2]}")
        continue
    old = subprocess.run(["git", "show", f"{base}:{parts[1]}"], cwd=REPO,
                         capture_output=True, text=True, check=True).stdout
    new = (REPO / parts[2]).read_text()
    inv = {v: k for k, v in LATER.items()}
    for o, n in QUALIFIED.get(parts[2], []) + QUALIFIED.get(inv.get(parts[2], ""), []):
        old = old.replace(o, n)
    for o, n in LATER_QUALIFIERS:
        old = re.sub(r"(?<![\w.'])" + o + r"\.(?=[A-Za-z_])", n + ".", old)
    if body(old) == body(new):
        verdict = "same"
    elif code(old) == code(new):
        verdict = "comments only"
    else:
        verdict = "BODY CHANGED"
        bad += 1
    print(f"{verdict}  {parts[1]} -> {parts[2]}")
sys.exit(1 if bad else 0)
