# Domain docs

## Layout and reading order

This repository uses a multi-context layout.

1. Read the root [CONTEXT-MAP.md](../../CONTEXT-MAP.md).
2. Read [Code/CONTEXT.md](../../Code/CONTEXT.md), then the parent and local
   contexts relevant to the task.
3. Follow cross-context links when a change spans areas.
4. Read relevant decisions in root `docs/adr/` or a context's own `docs/adr/`,
   when present. Proceed silently when optional contexts or ADRs are absent.

## Vocabulary and evidence

Use the terminology established in the local contexts and source definitions.
Check source declarations for exact types, orders, and theorem statements.
Discuss new terms with the user before adopting them.
Meeting notes are historical discussion rather than adopted ADRs; surface
conflicts with an existing ADR explicitly.

## Maintenance

Update affected contexts and the global map when directory roles, terminology,
or architectural relationships change. Coverage follows `Code/_CoqProject`,
including parent directories. Link to detailed documentation rather than
duplicating it, and describe the current checkout rather than another branch.

Use “healthy” and “healthiness” for predicate-transformer class conditions.
Use “well-formed” and “well-formedness” for general validity constraints.
Healthiness does not assert arrow or monad laws; see the root development rules.
