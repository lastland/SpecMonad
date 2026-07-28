# Domain Docs

How the engineering skills should consume this repo's domain documentation when exploring the codebase.

**This repo uses the multi-context layout.** The presence of `CONTEXT-MAP.md` at the repo root is the signal.

**Current live context: `Code/Taxonomy/`.** This is where active development happens. Other trees (`Code/Classes/`, etc.) exist as supporting infrastructure but are not currently being changed — don't spin up per-context glossaries or ADRs for them unless work moves there. `Taxonomy/deprecated/` is deliberately excluded from the build; ignore it.

## Before exploring, read these

- **`CONTEXT-MAP.md`** at the repo root — it points at one `CONTEXT.md` per context. Read each one relevant to the topic.
- **`docs/adr/`** — read ADRs that touch the area you're about to work in (system-wide decisions).
- **Context-scoped docs** — also check `<context>/docs/adr/` (or the per-context path recorded in `CONTEXT-MAP.md`) for decisions scoped to a single context.

If any of these files don't exist, **proceed silently**. Don't flag their absence; don't suggest creating them upfront. The `/domain-modeling` skill (reached via `/grill-with-docs` and `/improve-codebase-architecture`) creates them lazily when terms or decisions actually get resolved.

## File structure

Multi-context repo (this repo):

```
/
├── CONTEXT-MAP.md                     ← points at each per-context CONTEXT.md
├── docs/adr/                          ← system-wide decisions
└── Code/
    └── Taxonomy/                      ← the live context
        ├── CONTEXT.md
        └── docs/adr/                  ← context-specific decisions
```

Single-context (for reference — not this repo): a single `CONTEXT.md` + `docs/adr/` at the repo root.

## Use the glossary's vocabulary

When your output names a domain concept (in an issue title, a refactor proposal, a hypothesis, a test name), use the term as defined in the relevant `CONTEXT.md`. Don't drift to synonyms the glossary explicitly avoids.

If the concept you need isn't in the glossary yet, that's a signal — either you're inventing language the project doesn't use (reconsider) or there's a real gap (note it for `/domain-modeling`).

## Flag ADR conflicts

If your output contradicts an existing ADR, surface it explicitly rather than silently overriding:

> _Contradicts ADR-0007 (event-sourced orders) — but worth reopening because…_
