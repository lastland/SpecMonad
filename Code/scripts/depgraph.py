#!/usr/bin/env python3
"""Generate an interactive HTML dependency graph of the Coq files in _CoqProject.

Dependencies come from `coqdep -f _CoqProject`, so only edges between project
files are shown (Coq stdlib, ITree, ExtLib, ... are omitted).

Usage (from Code/):
    python3 scripts/depgraph.py [-o depgraph.html] [--coqdep coqdep]

Then open the generated file in a browser.  Click a node to inspect it; the
side panel lists direct and transitive dependencies / dependents.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

CODE = Path(__file__).resolve().parent.parent

DECL_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)*"
    r"(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example"
    r"|Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|Instance)\b",
    re.M,
)
ADMIT_RE = re.compile(r"\b(Admitted|admit)\b")
AXIOM_RE = re.compile(r"^\s*(Axiom|Parameter|Conjecture)\b", re.M)


def strip_comments(src: str) -> str:
    # Coq comments nest; strip innermost first until none remain.
    prev = None
    while prev != src:
        prev, src = src, re.sub(r"\(\*(?:(?!\(\*).)*?\*\)", " ", src, flags=re.S)
    return src


def project_files() -> list[str]:
    files = []
    for line in (CODE / "_CoqProject").read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line.endswith(".v") and not line.startswith("-"):
            files.append(line)
    return files


def run_coqdep(coqdep: str) -> dict[str, list[str]]:
    proc = subprocess.run(
        [coqdep, "-f", "_CoqProject"], cwd=CODE, capture_output=True, text=True
    )
    if not proc.stdout.strip():
        sys.exit(f"coqdep produced no output:\n{proc.stderr}")
    if proc.stderr.strip():
        print(proc.stderr.strip(), file=sys.stderr)
    deps: dict[str, list[str]] = {}
    for line in proc.stdout.splitlines():
        if ":" not in line:
            continue
        targets, prereqs = line.split(":", 1)
        vo = next((t for t in targets.split() if t.endswith(".vo")), None)
        if vo is None:
            continue
        src = vo[:-1]  # foo.vo -> foo.v
        deps[src] = sorted(
            {p[:-1] for p in prereqs.split() if p.endswith(".vo") and p[:-1] != src}
        )
    return deps


def file_stats(path: Path) -> dict:
    raw = path.read_text(errors="replace")
    src = strip_comments(raw)
    kinds: dict[str, int] = {}
    for m in DECL_RE.finditer(src):
        kinds[m.group(1)] = kinds.get(m.group(1), 0) + 1
    lemmas = sum(kinds.get(k, 0) for k in
                 ("Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark", "Example"))
    defs = sum(kinds.get(k, 0) for k in
               ("Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Record"))
    return {
        "lines": raw.count("\n") + 1,
        "lemmas": lemmas,
        "defs": defs,
        "classes": kinds.get("Class", 0),
        "instances": kinds.get("Instance", 0),
        "admits": len(ADMIT_RE.findall(src)),
        "axioms": len(AXIOM_RE.findall(src)),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-o", "--output", default="depgraph.html",
                    help="output HTML path, relative to Code/ (default: depgraph.html)")
    ap.add_argument("--coqdep", default="coqdep", help="coqdep executable")
    args = ap.parse_args()

    files = project_files()
    deps = run_coqdep(args.coqdep)
    known = set(files)
    nodes = []
    for f in files:
        p = CODE / f
        nodes.append({
            "id": f,
            "group": f.split("/")[0] if "/" in f else "(root)",
            "deps": [d for d in deps.get(f, []) if d in known],
            "stats": file_stats(p) if p.exists() else None,
        })

    html = TEMPLATE.replace("/*__DATA__*/null", json.dumps(nodes))
    out = (CODE / args.output).resolve()
    out.write_text(html)
    n_edges = sum(len(n["deps"]) for n in nodes)
    print(f"Wrote {out} ({len(nodes)} files, {n_edges} edges)")


TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Coq Dependency Graph</title>
<script src="https://cdn.jsdelivr.net/npm/cytoscape@3.30.2/dist/cytoscape.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/dagre@0.8.5/dist/dagre.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/cytoscape-dagre@2.5.0/cytoscape-dagre.min.js"></script>
<style>
:root {
  --bg: #fafaf9; --panel: #ffffff; --fg: #1c1917; --muted: #78716c; --border: #e7e5e4;
  --edge: #c4c0bc; --accent: #2563eb; --dep: #059669; --rdep: #d97706; --warn: #dc2626;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #1c1917; --panel: #292524; --fg: #f5f5f4; --muted: #a8a29e; --border: #44403c;
    --edge: #57534e; --accent: #60a5fa; --dep: #34d399; --rdep: #fbbf24; --warn: #f87171;
  }
}
* { box-sizing: border-box; }
html, body { margin: 0; height: 100%; background: var(--bg); color: var(--fg);
  font: 13px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif; }
#app { display: grid; grid-template-columns: 1fr 360px; height: 100vh; }
#cy { width: 100%; height: 100%; }
aside { background: var(--panel); border-left: 1px solid var(--border); overflow-y: auto; padding: 14px 16px; }
h1 { font-size: 15px; margin: 0 0 10px; }
h2 { font-size: 12px; text-transform: uppercase; letter-spacing: .05em; color: var(--muted); margin: 16px 0 6px; }
.row { display: flex; gap: 6px; flex-wrap: wrap; align-items: center; margin-bottom: 8px; }
input[type=search], select { flex: 1; min-width: 0; padding: 6px 8px; border: 1px solid var(--border);
  border-radius: 6px; background: var(--bg); color: var(--fg); font: inherit; }
button { padding: 5px 9px; border: 1px solid var(--border); border-radius: 6px; background: var(--bg);
  color: var(--fg); font: inherit; cursor: pointer; }
button:hover { border-color: var(--accent); }
label { display: flex; gap: 5px; align-items: center; color: var(--muted); cursor: pointer; }
.legend { display: flex; flex-wrap: wrap; gap: 4px 10px; }
.legend span { display: inline-flex; align-items: center; gap: 4px; cursor: pointer; }
.legend span.off { opacity: .35; }
.sw { width: 10px; height: 10px; border-radius: 3px; display: inline-block; }
ul { list-style: none; margin: 0; padding: 0; }
li { padding: 2px 0; cursor: pointer; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 12px;
  word-break: break-all; }
li:hover { color: var(--accent); }
li.direct::before { content: "● "; }
li.trans { color: var(--muted); }
li.trans::before { content: "○ "; }
.stats { display: grid; grid-template-columns: auto 1fr; gap: 2px 12px; font-size: 12px; }
.stats b { font-weight: 600; }
.warn { color: var(--warn); }
.sel { font-family: ui-monospace, monospace; font-size: 13px; word-break: break-all; font-weight: 600; }
.hint { color: var(--muted); font-size: 12px; }
.cycle { color: var(--warn); font-weight: 600; }
@media (max-width: 800px) { #app { grid-template-columns: 1fr; grid-template-rows: 60vh auto; } aside { border-left: 0; border-top: 1px solid var(--border); } }
</style>
</head>
<body>
<div id="app">
  <div id="cy"></div>
  <aside>
    <h1>Coq Dependency Graph</h1>
    <div class="row"><input id="search" type="search" placeholder="Find file… (Enter to select)" list="files"><datalist id="files"></datalist></div>
    <div class="row">
      <select id="layout">
        <option value="LR">Layout: left → right</option>
        <option value="TB">Layout: top → bottom</option>
        <option value="cose">Layout: force</option>
      </select>
      <button id="fit">Fit</button>
      <button id="clear">Clear</button>
    </div>
    <div class="row">
      <label><input id="reduce" type="checkbox" checked> Transitive reduction</label>
      <label><input id="focus" type="checkbox"> Show only selection's cone</label>
    </div>
    <div class="row">
      <label><input id="sizeByLines" type="checkbox" checked> Size by lines</label>
      <label><input id="markAdmits" type="checkbox" checked> Mark admits/axioms</label>
    </div>
    <h2>Directories</h2>
    <div class="legend" id="legend"></div>
    <div id="summary" class="hint" style="margin-top:10px"></div>
    <div id="details"><p class="hint">Click a node to see its dependencies (green, upstream) and dependents (orange, downstream). Double-click to open the cone only.</p></div>
  </aside>
</div>
<script>
const DATA = /*__DATA__*/null;
const PALETTE = ["#2563eb","#059669","#d97706","#db2777","#7c3aed","#0891b2","#65a30d","#dc2626","#9333ea","#0d9488","#ca8a04","#4f46e5"];
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();

// ---- graph data ------------------------------------------------------------
const byId = new Map(DATA.map(n => [n.id, n]));
const fwd = new Map(DATA.map(n => [n.id, n.deps]));            // file -> files it requires
const rev = new Map(DATA.map(n => [n.id, []]));
for (const n of DATA) for (const d of n.deps) rev.get(d).push(n.id);

function closure(start, adj) {
  const seen = new Set(), stack = [...(adj.get(start) || [])];
  while (stack.length) { const x = stack.pop(); if (seen.has(x)) continue; seen.add(x); stack.push(...(adj.get(x) || [])); }
  seen.delete(start); return seen;
}
const fwdClosure = new Map(DATA.map(n => [n.id, closure(n.id, fwd)]));
const revClosure = new Map(DATA.map(n => [n.id, closure(n.id, rev)]));

// Edge a->b is redundant if b is reachable from some other direct dep of a.
const redundant = new Set();
for (const n of DATA) for (const d of n.deps)
  if (n.deps.some(o => o !== d && fwdClosure.get(o).has(d))) redundant.add(n.id + "→" + d);

// Cycle detection (should be impossible with coqdep, but cheap to check).
const cyclic = DATA.filter(n => fwdClosure.get(n.id).has(n.id)).map(n => n.id);

const groups = [...new Set(DATA.map(n => n.group))].sort();
const color = Object.fromEntries(groups.map((g, i) => [g, PALETTE[i % PALETTE.length]]));
const hidden = new Set();

// ---- cytoscape -------------------------------------------------------------
const short = id => id.replace(/\.v$/, "");
const elements = [
  ...DATA.map(n => ({ data: {
    id: n.id, label: short(n.id).split("/").slice(-2).join("/"), group: n.group, color: color[n.group],
    lines: n.stats ? n.stats.lines : 0,
    bad: n.stats && (n.stats.admits + n.stats.axioms) > 0 ? 1 : 0 } })),
  ...DATA.flatMap(n => n.deps.map(d => ({ data: {
    id: n.id + "→" + d, source: n.id, target: d, redundant: redundant.has(n.id + "→" + d) ? 1 : 0 } }))),
];
const maxLines = Math.max(...DATA.map(n => n.stats ? n.stats.lines : 1));

const cy = cytoscape({
  container: document.getElementById("cy"),
  elements, wheelSensitivity: 0.2, minZoom: 0.05, maxZoom: 4,
  style: [
    { selector: "node", style: {
      "background-color": "data(color)", "label": "data(label)", "color": css("--fg"),
      "font-size": 10, "text-valign": "bottom", "text-margin-y": 3, "text-wrap": "none",
      "width": 18, "height": 18, "border-width": 0,
      "text-background-color": css("--bg"), "text-background-opacity": 0.75, "text-background-padding": 1 } },
    { selector: "node.sized", style: {
      "width": e => 12 + 30 * Math.sqrt(e.data("lines") / maxLines),
      "height": e => 12 + 30 * Math.sqrt(e.data("lines") / maxLines) } },
    { selector: "node.markbad[bad = 1]", style: { "border-width": 3, "border-color": css("--warn"), "border-style": "dashed" } },
    { selector: "edge", style: {
      "width": 1, "line-color": css("--edge"), "target-arrow-color": css("--edge"),
      "target-arrow-shape": "triangle", "arrow-scale": 0.7, "curve-style": "bezier", "opacity": 0.8 } },
    { selector: "edge.reduced[redundant = 1]", style: { "display": "none" } },
    { selector: ".faded", style: { "opacity": 0.12 } },
    { selector: "node.selected", style: { "border-width": 4, "border-color": css("--accent"), "border-style": "solid", "font-weight": "bold", "font-size": 12, "z-index": 10 } },
    { selector: "node.dep", style: { "border-width": 3, "border-color": css("--dep"), "border-style": "solid" } },
    { selector: "node.rdep", style: { "border-width": 3, "border-color": css("--rdep"), "border-style": "solid" } },
    { selector: "edge.dep", style: { "line-color": css("--dep"), "target-arrow-color": css("--dep"), "width": 2, "opacity": 1, "z-index": 5 } },
    { selector: "edge.rdep", style: { "line-color": css("--rdep"), "target-arrow-color": css("--rdep"), "width": 2, "opacity": 1, "z-index": 5 } },
    { selector: ".hidden", style: { "display": "none" } },
  ],
});

let selected = null;

function runLayout() {
  const v = document.getElementById("layout").value;
  const eles = cy.elements(":visible");
  const opts = v === "cose"
    ? { name: "cose", animate: false, nodeRepulsion: 9000, idealEdgeLength: 80, padding: 30 }
    : { name: "dagre", rankDir: v, nodeSep: 18, rankSep: 70, edgeSep: 6, padding: 30, animate: false };
  eles.layout(opts).run();
  eles.fit(undefined, 30);
}

function applyToggles() {
  const reduce = document.getElementById("reduce").checked;
  cy.edges().toggleClass("reduced", reduce);
  cy.nodes().toggleClass("sized", document.getElementById("sizeByLines").checked);
  cy.nodes().toggleClass("markbad", document.getElementById("markAdmits").checked);
}

function applyVisibility() {
  const focus = document.getElementById("focus").checked && selected;
  const cone = focus ? new Set([selected, ...fwdClosure.get(selected), ...revClosure.get(selected)]) : null;
  cy.batch(() => cy.nodes().forEach(n => {
    const hide = hidden.has(n.data("group")) || (cone && !cone.has(n.id()));
    n.toggleClass("hidden", !!hide);
  }));
}

function highlight() {
  cy.batch(() => {
    cy.elements().removeClass("faded selected dep rdep");
    if (!selected) return;
    const up = fwdClosure.get(selected), down = revClosure.get(selected);
    cy.elements().addClass("faded");
    const s = cy.getElementById(selected).removeClass("faded").addClass("selected");
    for (const id of up) cy.getElementById(id).removeClass("faded").addClass("dep");
    for (const id of down) cy.getElementById(id).removeClass("faded").addClass("rdep");
    cy.edges().forEach(e => {
      const a = e.source().id(), b = e.target().id();
      if ((a === selected || up.has(a)) && up.has(b)) e.removeClass("faded").addClass("dep");
      else if ((b === selected || down.has(b)) && down.has(a)) e.removeClass("faded").addClass("rdep");
    });
  });
}

const esc = s => s.replace(/[&<>]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
function list(ids, direct) {
  if (!ids.length) return '<p class="hint">none</p>';
  const sorted = [...ids].sort((a, b) => (direct.has(b) - direct.has(a)) || a.localeCompare(b));
  return "<ul>" + sorted.map(id => `<li class="${direct.has(id) ? "direct" : "trans"}" data-id="${esc(id)}">${esc(id)}</li>`).join("") + "</ul>";
}

function renderDetails() {
  const el = document.getElementById("details");
  if (!selected) { el.innerHTML = '<p class="hint">Click a node to see its dependencies (green, upstream) and dependents (orange, downstream). Double-click to show only its cone.</p>'; return; }
  const n = byId.get(selected), st = n.stats || {};
  const up = [...fwdClosure.get(selected)], down = [...revClosure.get(selected)];
  const directUp = new Set(n.deps), directDown = new Set(rev.get(selected));
  el.innerHTML = `
    <h2>Selected</h2><div class="sel">${esc(selected)}</div>
    <div class="stats" style="margin-top:8px">
      <span>Lines</span><b>${st.lines ?? "?"}</b>
      <span>Lemmas/theorems</span><b>${st.lemmas ?? "?"}</b>
      <span>Definitions</span><b>${st.defs ?? "?"}</b>
      <span>Classes / instances</span><b>${st.classes ?? "?"} / ${st.instances ?? "?"}</b>
      <span>Admits</span><b class="${st.admits ? "warn" : ""}">${st.admits ?? "?"}</b>
      <span>Axioms/params</span><b class="${st.axioms ? "warn" : ""}">${st.axioms ?? "?"}</b>
    </div>
    <h2 style="color:var(--dep)">Depends on — ${directUp.size} direct, ${up.length} total</h2>${list(up, directUp)}
    <h2 style="color:var(--rdep)">Used by — ${directDown.size} direct, ${down.length} total</h2>${list(down, directDown)}`;
  el.querySelectorAll("li[data-id]").forEach(li => li.onclick = () => select(li.dataset.id, true));
}

function select(id, center) {
  selected = id;
  highlight(); renderDetails();
  if (document.getElementById("focus").checked) { applyVisibility(); runLayout(); }
  if (id && center) cy.animate({ center: { eles: cy.getElementById(id) }, duration: 250 });
}

// ---- UI wiring -------------------------------------------------------------
cy.on("tap", "node", e => select(e.target.id(), false));
cy.on("tap", e => { if (e.target === cy) select(null); });
cy.on("dbltap", "node", e => {
  document.getElementById("focus").checked = true;
  select(e.target.id(), false); applyVisibility(); runLayout();
});

const legend = document.getElementById("legend");
for (const g of groups) {
  const count = DATA.filter(n => n.group === g).length;
  const s = document.createElement("span");
  s.innerHTML = `<i class="sw" style="background:${color[g]}"></i>${esc(g)} <span class="hint">${count}</span>`;
  s.onclick = () => { hidden.has(g) ? hidden.delete(g) : hidden.add(g); s.classList.toggle("off"); applyVisibility(); runLayout(); };
  legend.appendChild(s);
}

const dl = document.getElementById("files");
for (const n of DATA) { const o = document.createElement("option"); o.value = n.id; dl.appendChild(o); }
const search = document.getElementById("search");
search.addEventListener("keydown", e => {
  if (e.key !== "Enter") return;
  const q = search.value.trim().toLowerCase();
  const hit = DATA.find(n => n.id.toLowerCase() === q) || DATA.find(n => n.id.toLowerCase().includes(q));
  if (hit) select(hit.id, true);
});

document.getElementById("layout").onchange = runLayout;
document.getElementById("fit").onclick = () => cy.elements(":visible").fit(undefined, 30);
document.getElementById("clear").onclick = () => { document.getElementById("focus").checked = false; select(null); applyVisibility(); runLayout(); };
document.getElementById("reduce").onchange = () => { applyToggles(); runLayout(); };
document.getElementById("focus").onchange = () => { applyVisibility(); runLayout(); };
document.getElementById("sizeByLines").onchange = applyToggles;
document.getElementById("markAdmits").onchange = applyToggles;

const nEdges = DATA.reduce((a, n) => a + n.deps.length, 0);
const roots = DATA.filter(n => !rev.get(n.id).length).length;
const leaves = DATA.filter(n => !n.deps.length).length;
document.getElementById("summary").innerHTML =
  `${DATA.length} files · ${nEdges} edges (${redundant.size} transitively redundant) · ${leaves} with no project deps · ${roots} unused by others` +
  (cyclic.length ? `<br><span class="cycle">Cycle through: ${cyclic.map(esc).join(", ")}</span>` : "");

applyToggles();
runLayout();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    main()
