#!/usr/bin/env python3
"""Drop project imports that a file does not need.

    python3 docs/reorg/minimize_requires.py FILE.v ...      (paths relative to Code/)

For each project module a file requires (library modules are left alone),
try the file without it, compiling a copy against the current build; keep
the removal if it still compiles.  Candidates whose names the file never
mentions are tried all at once first, then one by one.  Afterwards rebuild
from scratch: a downstream file may have relied on an instance that is no
longer loaded on its behalf.
"""
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from move import CODE, SENTENCE, logical, project_files, resolve, render  # noqa: E402

FILES = project_files()


def requires(text):
    """(match, [(name, resolved project file or None)])"""
    out = []
    for m in SENTENCE.finditer(text):
        names = m.group("names").split()
        out.append((m, [(n, resolve(m.group("from"), n, FILES)) for n in names]))
    return out


def without(text, drop):
    """Text with the project modules in `drop` removed from Require sentences."""
    def sub(m):
        names = m.group("names").split()
        keep = [n for n in names if resolve(m.group("from"), n, FILES) not in drop]
        if len(keep) == len(names):
            return m.group(0)
        if not keep:
            return ""
        return render(m.group("indent"), m.group("kind"), [(m.group("from"), keep)],
                      "\n" in m.group("names"))
    return re.sub(r"\n{3,}", "\n\n", SENTENCE.sub(sub, text))


def compiles(rel, text):
    src = CODE / rel
    tmp = src.with_name("MinimizeTmp" + src.stem + ".v")
    tmp.write_text(text)
    try:
        r = subprocess.run(["coqc", "-q", "-Q", ".", "Incorrectness", str(tmp.relative_to(CODE))],
                           cwd=CODE, capture_output=True, text=True)
        return r.returncode == 0
    finally:
        for ext in (".v", ".vo", ".vos", ".vok", ".glob"):
            tmp.with_suffix(ext).unlink(missing_ok=True)
        aux = tmp.with_name("." + tmp.stem + ".aux")
        aux.unlink(missing_ok=True)


def declared(rel):
    t = (CODE / rel).read_text()
    return set(re.findall(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Program\s+)?(?:Theorem|Lemma|Definition|Corollary|"
                          r"Instance|Fixpoint|Inductive|Record|Class|Notation|Example)\s+([\w']+)", t, re.M))


def minimize(rel):
    text = (CODE / rel).read_text()
    code = re.sub(r"\(\*.*?\*\)", " ", SENTENCE.sub("", text), flags=re.S)
    mods = [r for _, ns in requires(text) for _, r in ns if r]
    if not mods:
        return []
    unused = [m for m in mods if not any(re.search(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", code)
                                         for n in declared(m))
              and Path(m).stem + "." not in code]
    dropped = []
    if unused and compiles(rel, without(text, set(unused))):
        dropped = list(unused)
    else:
        for m in unused:
            if compiles(rel, without(text, set(dropped) | {m})):
                dropped.append(m)
    for m in mods:   # the others: maybe only an instance source that is loaded anyway
        if m not in dropped and m not in unused and compiles(rel, without(text, set(dropped) | {m})):
            dropped.append(m)
    if dropped:
        (CODE / rel).write_text(without(text, set(dropped)))
    return dropped


if __name__ == "__main__":
    for rel in sys.argv[1:]:
        d = minimize(rel)
        print(f"{rel}: dropped {', '.join(Path(x).stem for x in d) or 'nothing'}", flush=True)
