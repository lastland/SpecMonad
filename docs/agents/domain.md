# Domain docs

## Layout and reading order

This repository uses a multi-context layout.

1. Read the root [CONTEXT-MAP.md](../../CONTEXT-MAP.md).
2. Read [Code/CONTEXT.md](../../Code/CONTEXT.md) and the parent and local
   contexts relevant to the work.
3. Follow cross-context links when the work spans multiple areas.
4. Read relevant architectural decisions under root `docs/adr/` or a
   context's own `docs/adr/`, when present.

Proceed silently when an optional context or ADR directory is absent.

## Vocabulary and evidence

Use the terminology established in the relevant context.
Check linked source definitions when exact types or semantics matter.
Use “well-formed” and “well-formedness” for SP transformer constraints.

Treat meeting notes as historical discussion rather than adopted
architectural decisions. Surface conflicts with existing ADRs.

## Maintenance

Update affected contexts and the global map when directory roles,
domain terminology, or architectural relationships change.
Link to detailed documentation instead of duplicating it.
