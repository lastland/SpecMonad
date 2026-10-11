#!/usr/bin/env python3
"""Snapshot every declaration of the build and its statement, to check that a
reorganization (moves and splits) neither loses nor changes anything.

    python3 scripts/inventory.py snapshot OUT.json   # after `make`, from Code/
    python3 scripts/inventory.py compare OLD.json NEW.json

`snapshot` reads the .glob file of each file in _CoqProject, collects the
declared names with their kind and module path, then runs coqc on a generated
file that prints each statement (`Set Printing All`) and its `About` facts
(implicit arguments, opacity, minus location lines), plus the instance
database of a file requiring the whole build.
`compare` matches declarations by (kind, module path, name) -- the file they
live in may change -- and compares their statements after replacing every
file qualifier (`Incorrectness.A.File.`, `File.`, `Alias.`) by `§`, so a lemma
moved to another file still compares equal while any change to its statement
does not.
"""

import json
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

CODE = Path(__file__).resolve().parent.parent
# .glob kinds that are declarations we can `Check`.
CHECKABLE = {"def", "prf", "inst", "ind", "constr", "rec", "proj", "class", "ax", "meth", "scheme"}
OTHER = {"not", "mod", "modtype", "coe", "abbrev", "syndef"}
GLOB_RE = re.compile(r"^(\w+) \d+:\d+ (\S+) (\S+)$")


def project():
    libs, files = [], []
    for line in (CODE / "_CoqProject").read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line.startswith(("-Q", "-R")):
            libs += line.split()
        elif line.endswith(".v"):
            files.append(line)
    return libs, files


def declarations(files):
    decls = []
    for f in files:
        glob = CODE / (f[:-2] + ".glob")
        if not glob.exists():
            sys.exit(f"missing {glob}: run make first")
        logical = None
        for line in glob.read_text().splitlines():
            if line.startswith("F"):
                logical = line[1:]
                continue
            m = GLOB_RE.match(line)
            if not m or (m.group(1) not in CHECKABLE and m.group(1) not in OTHER):
                continue
            kind, mpath, name = m.groups()
            mpath = "" if mpath == "<>" else mpath
            decls.append({"file": f, "logical": logical, "kind": kind, "mod": mpath, "name": name})
    return decls


def run_coq(libs, lines):
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "Inventory.v"
        src.write_text("\n".join(lines).replace("@OUT@", tmp) + "\n")
        proc = subprocess.run(["coqc", "-q", *libs, str(src)], cwd=CODE, capture_output=True, text=True)
        if proc.returncode != 0:
            sys.exit(f"coqc failed:\n{proc.stderr[-4000:]}")
        outs = {f.name: f.read_text() for f in Path(tmp).glob("*.out")}
    return proc.stdout, outs


# `About` lines that depend on where a declaration is, not what it is.
LOCATION = re.compile(r"^(Declared in|Expands to)|, line \d+, characters")


def statements(libs, decls):
    """Statement under `Set Printing All` and `About` facts of each declaration,
    and the instance database seen by a file that requires the whole build."""
    checkable = [d for d in decls if d["kind"] in CHECKABLE]
    lines = ["Set Printing Width 100000.", "Set Printing All."]
    lines += [f"Require {lg}." for lg in sorted({d['logical'] for d in decls})]
    for i, d in enumerate(checkable):
        full = ".".join(x for x in (d["logical"], d["mod"], d["name"]) if x)
        lines.append(f'Redirect "@OUT@/{i}c" Check @{full}.')
        lines.append(f'Redirect "@OUT@/{i}a" About {full}.')
    lines.append('Redirect "@OUT@/instances" Print HintDb typeclass_instances.')
    _, outs = run_coq(libs, lines)
    for i, d in enumerate(checkable):
        check = outs[f"{i}c.out"].strip().splitlines()
        d["statement"] = " ".join(x.strip() for x in check[1:])
        about = [x.strip() for x in outs[f"{i}a.out"].splitlines()]
        d["about"] = " | ".join(x for x in about if x and not LOCATION.search(x))
    return decls, outs["instances.out"].splitlines()


def snapshot(out):
    libs, files = project()
    decls, instances = statements(libs, declarations(files))
    logicals = sorted({d["logical"] for d in decls}, key=len, reverse=True)
    # `Module P := File.` makes Coq print `P.x` for a name of File; such
    # aliases are file qualifiers too.
    aliases = sorted({m.group(1) for f in files for m in re.finditer(
        r"^\s*Module\s+(\w+)\s*:=\s*[\w.]+\s*\.", (CODE / f).read_text(), re.M)})
    Path(out).write_text(json.dumps({"logicals": logicals + aliases, "decls": decls,
                                     "instances": instances}, indent=0))
    print(f"{len(decls)} declarations from {len(files)} files -> {out}")


def normalizer(logicals):
    # Coq prints the shortest unambiguous qualification, so a file path can
    # appear as any of its suffixes (A.B.File., B.File., File.).  Replace each
    # by `@`, longest first so A.B.File. is not cut at B.File.
    suffixes = {".".join(lg.split(".")[i:]) for lg in logicals for i in range(len(lg.split(".")))}
    pat = re.compile(r"(?<![\w.'])(?:" + "|".join(
        re.escape(x) for x in sorted(suffixes, key=len, reverse=True)) + r")\.")
    def norm(s):
        # Repeat: `File.Alias.x` needs two passes.  Collapse the markers.
        prev = None
        while prev != s:
            prev, s = s, pat.sub("§", s)
        return re.sub("§+", "§", s)
    return norm


def hints(lines, norm):
    """Individual hints of `Print HintDb`, one per instance and head.  The order
    within a head follows the order in which the snapshot file loads modules,
    which is alphabetical by path, so it is not compared; evar numbers neither."""
    out, head = [], None
    for line in lines:
        m = re.match(r"^For (.+?) ->\s*(.*)$", line)
        if not m:
            continue
        head, rest = m.groups()
        for h in re.split(r"(?<=, id \d\))\s*|(?<=, id \d\d\))\s*", rest):
            if h.strip():
                out.append(norm(re.sub(r"\?M\d+", "?M", f"{head} -> {h.strip()}")))
    return out


def compare(old_path, new_path):
    old, new = (json.loads(Path(p).read_text()) for p in (old_path, new_path))
    norm = normalizer(sorted(set(old["logicals"]) | set(new["logicals"]), key=len, reverse=True))
    key = lambda d: (d["kind"], d["mod"], d["name"])
    val = lambda d: norm(d.get("statement", "") + " || " + d.get("about", ""))
    # Notations and modules are compared by presence: a split may duplicate a
    # Local Notation into both halves without adding anything.
    count = lambda ds: Counter({k: (1 if k[0][0] in OTHER else c) for k, c in
                                Counter((key(d), val(d)) for d in ds).items()})
    o, n = count(old["decls"]), count(new["decls"])
    lost, gained = o - n, n - o
    # Report moves for names declared once on each side.
    once = lambda ds: {k: f for k, f in ((key(d), d["file"]) for d in ds)
                       if sum(1 for e in ds if key(e) == k) == 1}
    where_old, where_new = once(old["decls"]), once(new["decls"])
    moved = Counter((where_old[k], f) for k, f in where_new.items()
                    if k in where_old and where_old[k] != f)
    print(f"old {sum(o.values())} declarations, new {sum(n.values())}")
    for (a, b), c in sorted(moved.items()):
        print(f"  moved {c:4} {a} -> {b}")
    for label, diff in (("only in old", lost), ("only in new", gained)):
        for (k, st), c in sorted(diff.items()):
            print(f"{label}: {c}x {k[0]} {'.'.join(x for x in k[1:] if x)} : {st[:200]}")
    oi, ni = hints(old["instances"], norm), hints(new["instances"], norm)
    co, cn = Counter(oi), Counter(ni)
    same_set = set(co) == set(cn)
    copies = Counter((co[h], cn[h]) for h in co if h in cn and co[h] != cn[h])
    print(f"instance database: {'same' if same_set else 'DIFFERENT'} ({len(cn)} distinct hints)")
    for (a, b), c in sorted(copies.items()):
        # A module alias (`Module P := File.`) registers File's instances again.
        print(f"  warning: {c} hints registered {a}x before, {b}x now")
    if not same_set:
        for x in sorted(set(co) - set(cn)):
            print("  instance only in old:", x[:200])
        for x in sorted(set(cn) - set(co)):
            print("  instance only in new:", x[:200])
    ok = not lost and not gained and same_set
    print("OK: same declarations, statements and instances" if ok else "DIFFERENT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "snapshot":
        snapshot(sys.argv[2])
    elif len(sys.argv) == 4 and sys.argv[1] == "compare":
        compare(sys.argv[2], sys.argv[3])
    else:
        sys.exit(__doc__)
