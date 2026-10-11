#!/usr/bin/env python3
"""Partition Coq files by setting (generic / base / state / state+exceptions).

    python3 docs/reorg/partition.py SPEC.py [--dry-run]

SPEC.py defines SOURCES (Code/-relative paths, in dependency order), TARGET
(source, level) -> path, OVERRIDE {source: level or {decl name: level}},
HEADER {target: comment}, and ORDER (target files in layer order).

Each source is cut into units: one command with its proof, its trailing
`Arguments`, and the comments before it.  Inside a section, `Context`,
`Variable(s)`, `Hypothesis`, `Local Notation`... are the section's preamble
and are copied into every target that takes a unit of that section, between
copies of `Section X.` / `End X.`.  A unit's level is the highest of the
setting its own code names and the levels of the units it uses, so a
generic unit never depends on a setting.  Each target gets the import block
of its sources plus `Require Import` of the other targets it uses.
Qualified references `Source.name` anywhere in Code/ and in Markdown are
rewritten to the target that now declares `name`.
"""
import re
import runpy
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from move import CODE, logical, project_files  # noqa: E402
from split import code_lines  # noqa: E402

REPO = CODE.parent
LEVELS = ["Generic", "Base", "State", "StateExc"]
RANK = {"Generic": 0, "Base": 1, "State": 2, "StateExc": 2}
KEYWORDS = [
    ("StateExc", r"stdivexcndNE|StExc|optionT_map|LiftedEdgesExc|DiagramExc|_exc\b"),
    ("State", r"stdivndNE|\w*St\b|\w*St_\w*|stateT_map|LiftedEdges\b"),
    ("Base", r"\bdivndNE\b|\bdivnd\b|\bSetM\b|\w+Pure\b|\w+Pure_\w*|\bWPure\b|\bNE\b|retNE|bindNE"),
]
PREAMBLE = re.compile(r"^\s*(Context|Variables?|Hypothes[ie]s|Implicit Types?|Local Notation|"
                      r"#\[local\]\s+Notation|Let|Local Open Scope|Open Scope)\b")
STATEMENT = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)*(?:Local\s+|Global\s+|Polymorphic\s+)*(?:Program\s+)?"
                       r"(Theorem|Lemma|Corollary|Fact|Remark|Proposition|Example|Definition|Fixpoint|"
                       r"CoFixpoint|Instance|Inductive|CoInductive|Record|Class|Structure|Notation|"
                       r"Infix|Coercion|Ltac|Hint|Existing\s+Instance)\b\s*([\w'@.]*)")
PROOF_END = re.compile(r"^\s*(Qed|Defined|Admitted|Abort|Save)\b")


def sentences(text):
    """Split into (start, end, kind) pieces: kind is 'comment', 'space' or 'cmd'."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            d, j = 0, i
            while j < n:
                if text.startswith("(*", j):
                    d += 1; j += 2
                elif text.startswith("*)", j):
                    d -= 1; j += 2
                    if d == 0:
                        break
                else:
                    j += 1
            out.append((i, j, "comment")); i = j
        elif text[i].isspace():
            j = i
            while j < n and text[j].isspace():
                j += 1
            out.append((i, j, "space")); i = j
        else:
            j = i
            while j < n:
                if text.startswith("(*", j):
                    d, k = 0, j
                    while k < n:
                        if text.startswith("(*", k):
                            d += 1; k += 2
                        elif text.startswith("*)", k):
                            d -= 1; k += 2
                            if d == 0:
                                break
                        else:
                            k += 1
                    j = k; continue
                if text[j] == '"':
                    j = text.index('"', j + 1) + 1; continue
                if text[j] == "." and (j + 1 == n or text[j + 1].isspace()) and not text.startswith("..", j - 1):
                    j += 1; break
                j += 1
            out.append((i, j, "cmd")); i = j
    return out


def units(text):
    """Units: (text, kind, section, names) with kind in header/require/preamble/
    section-open/section-close/shared/decl."""
    pieces = sentences(text)
    cmds = [(a, b) for a, b, k in pieces if k == "cmd"]
    # attach preceding comments/space to each command
    res, pending, ci = [], "", 0
    first_comment_done = False
    header = ""
    for a, b, k in pieces:
        chunk = text[a:b]
        if k != "cmd":
            if k == "comment" and not first_comment_done and not res and not pending.strip():
                header = chunk; first_comment_done = True; continue
            pending += chunk; continue
        res.append([pending, chunk]); pending = ""
    trailing = pending
    # group proofs with their statements
    out, i, section = [], 0, []
    while i < len(res):
        pre, cmd = res[i]
        s = cmd.strip()
        m_sec = re.match(r"^(Section|Module)\s+(\w+)\.$", s)
        m_end = re.match(r"^End\s+(\w+)\.$", s)
        if m_sec and not s.startswith("Module Type"):
            section.append(m_sec.group(2)); out.append([pre, cmd, "section-open", tuple(section), []]); i += 1; continue
        if m_end and section and m_end.group(1) == section[-1]:
            out.append([pre, cmd, "section-close", tuple(section), []]); section.pop(); i += 1; continue
        if re.match(r"^(From\s+\S+\s+)?Require\b", s):
            out.append([pre, cmd, "require", tuple(section), []]); i += 1; continue
        if PREAMBLE.match(s) and section:
            out.append([pre, cmd, "preamble", tuple(section), []]); i += 1; continue
        if re.match(r"^(Import|Export|Open Scope|Local Open Scope|Set|Unset|Local Obligation Tactic|Obligation Tactic)\b", s) \
                or (PREAMBLE.match(s) and not section):
            out.append([pre, cmd, "shared", tuple(section), []]); i += 1; continue
        m = STATEMENT.match(s)
        if re.match(r"^Arguments\s+([\w'@.]+)", s) and out and out[-1][2] == "decl":
            out[-1][1] += pre + cmd; i += 1; continue
        body = pre + cmd; j = i + 1
        needs_proof = bool(m) and (m.group(1) in ("Theorem", "Lemma", "Corollary", "Fact", "Remark",
                                                   "Proposition", "Example")
                                   or (m.group(1) in ("Definition", "Instance", "Fixpoint")
                                       and ":=" not in s))
        if j < len(res) and re.match(r"^\s*(Proof|Next Obligation)\b", res[j][1]):
            needs_proof = True
        if needs_proof:
            while j < len(res):
                body += res[j][0] + res[j][1]
                if PROOF_END.match(res[j][1]):
                    j += 1
                    # further obligations
                    if j < len(res) and re.match(r"^\s*Next Obligation\b", res[j][1]):
                        continue
                    break
                j += 1
        names = []
        if m and m.group(2):
            names.append(m.group(2).lstrip("@"))
        for nm in re.findall(r"\|\s*([A-Za-z_][\w']*)\b", cmd) if m and m.group(1) in ("Inductive", "CoInductive") else []:
            names.append(nm)
        for nm in re.findall(r"([A-Za-z_][\w']*)\s*:", cmd.split(":=", 1)[1].split("}", 1)[0]) \
                if m and m.group(1) in ("Record", "Class", "Structure") and ":=" in cmd else []:
            names.append(nm)
        out.append([body[:len(pre)], body[len(pre):], "decl", tuple(section), names])
        i = j
    return header, out, trailing


def strip_comments(t):
    prev = None
    while prev != t:
        prev, t = t, re.sub(r"\(\*(?:(?!\(\*).)*?\*\)", " ", t, flags=re.S)
    return t


def own_level(code):
    for lv, pat in KEYWORDS:
        if re.search(pat, code):
            return lv
    return "Generic"


def main():
    spec = runpy.run_path(sys.argv[1])
    dry = "--dry-run" in sys.argv
    SOURCES, TARGET, OVERRIDE = spec["SOURCES"], spec["TARGET"], spec.get("OVERRIDE", {})
    data = {}
    for src in SOURCES:
        header, us, trailing = units((CODE / src).read_text())
        data[src] = (header, us, trailing)
    # global name -> (src, unit index)
    decl_of = {}
    for src in SOURCES:
        for k, u in enumerate(data[src][1]):
            if u[2] == "decl":
                for nm in u[4]:
                    decl_of.setdefault(nm, (src, k))
    tok = re.compile(r"[A-Za-z_][\w']*")
    level = {}
    for src in SOURCES:
        ov = OVERRIDE.get(src)
        for k, u in enumerate(data[src][1]):
            if u[2] != "decl":
                continue
            code = strip_comments(u[1])
            lv = own_level(code)
            if isinstance(ov, str):
                lv = ov
            elif isinstance(ov, dict):
                for nm in u[4]:
                    if nm in ov:
                        lv = ov[nm]
                sec = "/".join(u[3])
                if "@section:" + sec in ov:
                    lv = ov["@section:" + sec]
            level[(src, k)] = lv
    # propagate: a unit's level is at least that of what it uses
    uses = {}
    for src in SOURCES:
        for k, u in enumerate(data[src][1]):
            if u[2] == "decl":
                refs = set()
                for t in set(tok.findall(strip_comments(u[1]))):
                    d = decl_of.get(t)
                    if d and d != (src, k):
                        refs.add(d)
                uses[(src, k)] = refs
    changed = True
    while changed:
        changed = False
        for key, refs in uses.items():
            for r in refs:
                a, b = level[key], level[r]
                if RANK[b] > RANK[a] or (RANK[a] == RANK[b] == 2 and a != b):
                    if RANK[a] == RANK[b] == 2 and a != b:
                        sys.exit(f"{key} ({a}) uses {r} ({b})")
                    if isinstance(OVERRIDE.get(key[0]), str):
                        continue
                    level[key] = b; changed = True
    # assemble targets
    tgt_units = defaultdict(list)   # target -> list of (src, k)
    for src in SOURCES:
        for k, u in enumerate(data[src][1]):
            if u[2] == "decl":
                tgt_units[TARGET[(src, level[(src, k)])]].append((src, k))
    name_target = {}
    for t, lst in tgt_units.items():
        for src, k in lst:
            for nm in data[src][1][k][4]:
                name_target.setdefault(nm, t)
    out_text = {}
    order = spec["ORDER"]
    target_level = {}
    for (src, lv), t in TARGET.items():
        if t and (t not in target_level or RANK[lv] > RANK[target_level[t]]):
            target_level[t] = lv
    files_all = project_files()
    from move import SENTENCE as _S, resolve as _resolve
    src_requires = {}
    for s0 in SOURCES:
        reqs = []
        for m in _S.finditer((CODE / s0).read_text()):
            for nm in m.group("names").split():
                r = _resolve(m.group("from"), nm, files_all)
                if r in SOURCES and r != s0 and r not in reqs:
                    reqs.append(r)
        src_requires[s0] = reqs
    for t in order:
        if t not in tgt_units:
            continue
        srcs = [s for s in SOURCES if any(x[0] == s for x in tgt_units[t])]
        chosen = set(tgt_units[t])
        # imports: the sources' requires, then targets this one uses
        req = []
        for s in srcs:
            for u in data[s][1]:
                if u[2] == "require" and u[1].strip() not in [r.strip() for r in req]:
                    req.append(u[1].strip())
        used_t = []
        for key in tgt_units[t]:
            for r in uses[key]:
                tt = TARGET[(r[0], level[r])]
                if tt != t and tt not in used_t:
                    used_t.append(tt)
        # Instances are found without being named: also import the targets of
        # every source these sources required (and of the sources themselves),
        # at the levels this target may see.
        lv_t = target_level[t]
        allowed = {"Generic": {"Generic"}, "Base": {"Generic", "Base"},
                   "State": {"Generic", "Base", "State"},
                   "StateExc": {"Generic", "Base", "StateExc"}}[lv_t]
        for s in srcs:
            for r in [s] + src_requires[s]:
                for lv in allowed:
                    tt = TARGET.get((r, lv))
                    if tt and tt != t and tt in tgt_units and tt not in used_t \
                            and order.index(tt) < order.index(t):
                        used_t.append(tt)
        used_t.sort(key=order.index)
        # drop requires of the sources themselves (they are split away)
        srcmods = {Path(s).stem for s in SOURCES}
        def keep(r):
            names = r.rstrip(".").split()
            mods = names[names.index("Import") + 1:] if "Import" in names else names[names.index("Require") + 1:]
            return not (set(mods) & srcmods)
        req = [r for r in req if keep(r)]
        for tt in used_t:
            p, m = logical(tt).rsplit(".", 1)
            req.append(f"From {p} Require Import {m}.")
        body = []
        for s in srcs:
            for u in data[s][1]:
                if u[2] == "shared":
                    body.append(u[0] + u[1])
            us = data[s][1]
            # which sections does this target touch
            touched = {us[k][3] for (ss, k) in tgt_units[t] if ss == s}
            touched = {sec[:i] for sec in touched for i in range(1, len(sec) + 1)}
            for k, u in enumerate(us):
                if u[2] == "decl" and (s, k) in chosen:
                    body.append(u[0] + u[1])
                elif u[2] in ("section-open", "section-close", "preamble") and u[3] in touched:
                    body.append(u[0] + u[1])
        head = spec["HEADER"][t].rstrip() + "\n\n"
        text = head + "\n".join(req) + "\n" + "".join(body).rstrip() + "\n"
        out_text[t] = text
    if dry:
        for t in order:
            if t in tgt_units:
                n = len(tgt_units[t])
                print(f"{t:52} {n:4} units  {len(out_text[t].splitlines()):5} lines")
        return
    # write, git-moving each source onto its first target for history
    first = {}
    for src in SOURCES:
        ts = [TARGET[(src, level[(src, k)])] for k, u in enumerate(data[src][1]) if u[2] == "decl"]
        main = spec.get("MAIN", {}).get(src) or max(set(ts), key=ts.count)
        if main not in first.values():
            first[src] = main
    for src, t in first.items():
        (CODE / t).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", src, t], cwd=CODE, check=True)
    for src in SOURCES:
        if src not in first:
            subprocess.run(["git", "rm", "-q", src], cwd=CODE, check=True)
    for t, text in out_text.items():
        (CODE / t).parent.mkdir(parents=True, exist_ok=True)
        (CODE / t).write_text(text)
    subprocess.run(["git", "add", *out_text], cwd=CODE, check=True)
    # _CoqProject: replace the sources by the targets, in layer order
    proj = (CODE / "_CoqProject").read_text().splitlines()
    srcset = set(SOURCES)
    idx = min(i for i, l in enumerate(proj) if l.strip() in srcset)
    proj = [l for l in proj if l.strip() not in srcset]
    proj[idx:idx] = [t for t in order if t in out_text]
    (CODE / "_CoqProject").write_text("\n".join(proj) + "\n")
    # importers outside: require every target of the sources they named
    src_targets = defaultdict(list)
    for src in SOURCES:
        for t in order:
            if any(x[0] == src for x in tgt_units.get(t, [])) and t not in src_targets[src]:
                src_targets[src].append(t)
    files = project_files()
    from move import SENTENCE, resolve, render
    for p in list(CODE.rglob("*.v")):
        rel = str(p.relative_to(CODE))
        if rel.startswith(("Backup/", "ITreeExamples/")) or rel in out_text:
            continue
        txt = p.read_text()

        def sub(m):
            prefix, names = m.group("from"), m.group("names").split()
            resolved = [resolve(prefix, nm, files + SOURCES) for nm in names]
            if not any(r in srcset for r in resolved):
                return m.group(0)
            groups = []
            for nm, r in zip(names, resolved):
                targets = src_targets[r] if r in srcset else [r] if r else [None]
                for tt in targets:
                    pp, short = logical(tt).rsplit(".", 1) if tt else (prefix, nm)
                    if groups and groups[-1][0] == pp and short not in groups[-1][1]:
                        groups[-1][1].append(short)
                    elif not groups or groups[-1][0] != pp:
                        groups.append((pp, [short]))
            return render(m.group("indent"), m.group("kind"), groups, "\n" in m.group("names"))
        new = SENTENCE.sub(sub, txt)
        if new != txt:
            p.write_text(new)
    # qualified references Source.name -> Target.name
    moved = {}
    for nm, t in name_target.items():
        src = decl_of[nm][0]
        if Path(src).stem != Path(t).stem:
            moved[(Path(src).stem, nm)] = Path(t).stem
    pat = re.compile(r"(?<![\w.'])(" + "|".join(sorted({s for s, _ in moved}, key=len, reverse=True))
                     + r")\.([A-Za-z_][\w']*)")
    def requal(m):
        t = moved.get((m.group(1), m.group(2)))
        return f"{t}.{m.group(2)}" if t else m.group(0)
    paths = [p for p in CODE.rglob("*.v") if not str(p.relative_to(CODE)).startswith(("Backup/", "ITreeExamples/"))]
    paths += [p for p in REPO.rglob("*.md") if not str(p.relative_to(REPO)).startswith(
        ("docs/reorg/", "docs/reorg-plan.md", "docs/meeting-notes", "docs/removed-files.md", "Code/Backup"))]
    for p in paths:
        txt = p.read_text(); new = pat.sub(requal, txt)
        if new != txt:
            p.write_text(new)
    (REPO / "docs/reorg/partition-map.txt").write_text(
        "\n".join(f"{s}.{n} -> {t}.{n}" for (s, n), t in sorted(moved.items())) + "\n")
    # conservation: code lines of the targets = code lines of the sources
    # plus copies of section open/close/preamble lines
    from collections import Counter
    before = Counter()
    for s in SOURCES:
        before += Counter(code_lines((CODE / "..").joinpath("Code").joinpath(s).read_text()) if False else [])
    print(f"wrote {len(out_text)} files; moved {len(moved)} qualified names")


if __name__ == "__main__":
    main()
