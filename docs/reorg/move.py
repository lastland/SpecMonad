#!/usr/bin/env python3
"""Move Coq files and rewrite every `Require` sentence that names them.

    python3 docs/reorg/move.py OLD.v=NEW.v [OLD2.v=NEW2.v ...]

Paths are relative to Code/.  For each pair: `git mv`, update _CoqProject,
then rewrite the Require sentences of every .v file under Code/ (outside the
excluded directories) so that each module is required from its new directory.

A sentence `From P Require Import a b c.` is parsed into its modules; each is
resolved the way Coq does (P.m, or any project module under P ending in .m).
Modules are regrouped by their new directory, keeping their order, so a
sentence may become several consecutive ones.  Sentences that name no moved
module are left byte-identical.
"""

import re
import subprocess
import sys
from pathlib import Path

CODE = Path(__file__).resolve().parents[2] / "Code"
ROOT = "Incorrectness"
EXCLUDED = ("Backup/", "ITreeExamples/", "Taxonomy/deprecated/")
SENTENCE = re.compile(
    r"(?P<indent>^[ \t]*)(?:From[ \t\n]+(?P<from>[\w.']+)[ \t\n]+)?Require"
    r"(?:[ \t\n]+(?P<kind>Import|Export))?(?P<names>(?:[ \t\n]+[\w.']+?)+)\.(?=\s|$)",
    re.M)


def logical(path: str) -> str:
    return ".".join([ROOT, *path[:-2].split("/")])


def project_files() -> list[str]:
    return [l.strip() for l in (CODE / "_CoqProject").read_text().splitlines()
            if l.strip().endswith(".v") and not l.startswith("-")]


def resolve(prefix: str | None, name: str, files: list[str]) -> str | None:
    """The project file a `From prefix Require name` loads, if any."""
    full = f"{prefix}.{name}" if prefix else name
    exact = [f for f in files if logical(f) == full]
    if exact:
        return exact[0]
    under = prefix or ""
    cands = [f for f in files if logical(f).endswith("." + name)
             and (not under or logical(f).startswith(under + "."))]
    if len(cands) > 1:
        sys.exit(f"ambiguous Require {full}: {cands}")
    return cands[0] if cands else None


def render(indent, kind, groups, multiline):
    out = []
    for prefix, names in groups:
        head = f"{indent}{'From ' + prefix + ' ' if prefix else ''}Require{' ' + kind if kind else ''}"
        if multiline and len(names) > 1:
            out.append(head + "\n" + "\n".join(f"{indent}  {n}" for n in names[:-1])
                       + f"\n{indent}  {names[-1]}.")
        else:
            out.append(f"{head} {' '.join(names)}.")
    return "\n".join(out)


def rewrite(text: str, moves: dict[str, str], files: list[str]) -> str:
    def sub(m):
        prefix, names = m.group("from"), m.group("names").split()
        resolved = [resolve(prefix, n, files) for n in names]
        if not any(r in moves for r in resolved):
            return m.group(0)
        groups = []
        for n, r in zip(names, resolved):
            if r is not None:
                new = moves.get(r, r)
                p, short = logical(new).rsplit(".", 1)
            else:
                p, short = prefix, n
            if groups and groups[-1][0] == p:
                groups[-1][1].append(short)
            else:
                groups.append((p, [short]))
        return render(m.group("indent"), m.group("kind"), groups, "\n" in m.group("names"))
    return SENTENCE.sub(sub, text)


def main():
    moves = {}
    for arg in sys.argv[1:]:
        old, new = arg.split("=")
        moves[old] = new
    files = project_files()
    missing = [o for o in moves if o not in files]
    if missing:
        sys.exit(f"not in _CoqProject: {missing}")
    sources = [p for p in CODE.rglob("*.v")
               if not str(p.relative_to(CODE)).startswith(EXCLUDED)]
    # Rewrite before moving, while every name still resolves to its old file.
    for p in sources:
        text = p.read_text()
        new = rewrite(text, moves, files)
        if new != text:
            p.write_text(new)
    for old, new in moves.items():
        (CODE / new).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", old, new], cwd=CODE, check=True)
    proj = (CODE / "_CoqProject").read_text().splitlines()
    (CODE / "_CoqProject").write_text("\n".join(moves.get(l.strip(), l) for l in proj) + "\n")


if __name__ == "__main__":
    main()
