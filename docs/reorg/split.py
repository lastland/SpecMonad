#!/usr/bin/env python3
"""Split one Coq file into several, then rewrite the Requires that named it.

    python3 docs/reorg/split.py SPEC.py

SPEC.py defines (paths relative to Code/):

    SOURCE = "WP/WPureMonad.v"
    PARTS = [  # the first part keeps the file's git history
        ("WP/WPure.v", HEADER1, [(1, 244)]),          # 1-based, inclusive
        ("WP/WPVariants.v", HEADER2, [(245, None)]),
    ]
    # Which parts each importer needs; importers not listed get every part.
    USES = {"Taxonomy/MonadTaxonomy.v": ["WP/WPure.v", "WP/WPVariants.v"],
            "*": ["WP/WPure.v"]}
    # Qualified references to rewrite, per file: (old text, new text).
    QUALIFIED = {"Checks/Assumptions.v": [("WPureMonad.OrderedMonad_WPSub", "WPVariants.OrderedMonad_WPSub")]}

Each HEADER is the new file's opening comment and Require sentences; the
ranges are copied verbatim after it.  `--check REV` afterwards verifies that
the parts' code, comments and Requires removed, is the source's code at REV
plus only the lines listed in SPEC.DUPLICATED.
"""

import re
import runpy
import subprocess
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from move import CODE, SENTENCE, logical, project_files, resolve, render  # noqa: E402


def strip_comments(text):
    prev = None
    while prev != text:
        prev, text = text, re.sub(r"\(\*(?:(?!\(\*).)*?\*\)", " ", text, flags=re.S)
    return text


def code_lines(text):
    return [" ".join(l.split()) for l in SENTENCE.sub("", strip_comments(text)).splitlines() if l.strip()]


def rewrite_requires(text, source, uses):
    files = project_files()

    def sub(m):
        prefix, names = m.group("from"), m.group("names").split()
        resolved = [resolve(prefix, n, files) for n in names]
        if source not in resolved:
            return m.group(0)
        groups = []
        for n, r in zip(names, resolved):
            targets = uses if r == source else [r] if r else [None]
            for t in targets:
                p, short = logical(t).rsplit(".", 1) if t else (prefix, n)
                if groups and groups[-1][0] == p:
                    groups[-1][1].append(short)
                else:
                    groups.append((p, [short]))
        return render(m.group("indent"), m.group("kind"), groups, "\n" in m.group("names"))
    return SENTENCE.sub(sub, text)


def split(spec):
    src = CODE / spec["SOURCE"]
    lines = src.read_text().splitlines(keepends=True)
    parts = spec["PARTS"]
    bodies = []
    for path, header, ranges in parts:
        body = "".join("".join(lines[a - 1:(b if b else len(lines))]) for a, b in ranges)
        bodies.append((header.rstrip("\n") + "\n\n" if header.strip() else "") + body.lstrip("\n"))
    # Rewrite importers first, while the source still resolves.
    uses = spec["USES"]
    for p in CODE.rglob("*.v"):
        rel = str(p.relative_to(CODE))
        if rel.startswith(("Backup/", "ITreeExamples/")) or rel == spec["SOURCE"]:
            continue
        text = p.read_text()
        new = rewrite_requires(text, spec["SOURCE"], uses.get(rel, uses["*"]))
        for old, repl in spec.get("QUALIFIED", {}).get(rel, []):
            assert old in new, f"{rel}: {old!r} not found"
            new = new.replace(old, repl)
        if new != text:
            p.write_text(new)
    first = parts[0][0]
    (CODE / first).parent.mkdir(parents=True, exist_ok=True)
    if first != spec["SOURCE"]:
        subprocess.run(["git", "mv", spec["SOURCE"], first], cwd=CODE, check=True)
    for (path, _, _), body in zip(parts, bodies):
        (CODE / path).parent.mkdir(parents=True, exist_ok=True)
        (CODE / path).write_text(body)
    subprocess.run(["git", "add", *[p for p, _, _ in parts]], cwd=CODE, check=True)
    proj = (CODE / "_CoqProject").read_text().splitlines()
    out = []
    for l in proj:
        out += [p for p, _, _ in parts] if l.strip() == spec["SOURCE"] else [l]
    (CODE / "_CoqProject").write_text("\n".join(out) + "\n")


def check(spec, rev):
    old = subprocess.run(["git", "show", f"{rev}:Code/{spec['SOURCE']}"], cwd=CODE,
                         capture_output=True, text=True, check=True).stdout
    new = "".join((CODE / p).read_text() for p, _, _ in spec["PARTS"])
    o, n = Counter(code_lines(old)), Counter(code_lines(new))
    missing, extra = o - n, n - o
    allowed = Counter(" ".join(l.split()) for l in spec.get("DUPLICATED", []))
    unexpected = extra - allowed
    for l in missing.elements():
        print("missing from parts:", l)
    for l in unexpected.elements():
        print("unexpected in parts:", l)
    print(f"split check: {len(o)} code lines; duplicated {sum((extra & allowed).values())}; "
          + ("OK" if not missing and not unexpected else "FAILED"))
    sys.exit(0 if not missing and not unexpected else 1)


if __name__ == "__main__":
    spec = runpy.run_path(sys.argv[1])
    if len(sys.argv) == 4 and sys.argv[2] == "--check":
        check(spec, sys.argv[3])
    else:
        split(spec)
