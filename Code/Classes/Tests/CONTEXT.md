# Classes tests

Parent: [Classes context](../CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../../CLAUDE.md).

## Scope

[ArrowMonadRegression.v](ArrowMonadRegression.v) protects the generic
arrow-derived monad and its application-law contract. It imports
[Arrow.v](../Arrow.v), [ArrowMonad.v](../ArrowMonad.v), ITree's monad laws,
and Coq equality infrastructure, without importing Taxonomy carriers.

## What the regression establishes

- `WrongIndex.t A B := (bool -> A) -> bool -> B` supplies an arrow with
  proved core laws and an application operation that selects the stored
  arrow at `negb i`.
- `fixed_application` shows that this operation satisfies fixed-arrow
  application. `right_identity_fails` shows that this alone does not make
  the derived bind lawful.
- `application_contract_rejects_wrong_index` proves that the full
  `ArrowApplyLaws` contract rejects this implementation, using `app_unit`.
- `GenericResolution` checks `MonadLawsE` and `Eq1Equivalence` resolution for
  the exact `Monad_Arrow` operations and explicit `Eq1_Arrow`, for every
  fixed input type `I`.

## Reading and build membership

Read the application fields in `Arrow.v`, then `WrongIndex`, then
`GenericResolution`. The regression is listed in
[_CoqProject](../../_CoqProject), so it belongs to the normal build.

[Taxonomy tests](../../Taxonomy/Arrows/Tests/CONTEXT.md) serve a different scope:
[ArrowMonadInstances.v](../../Taxonomy/Arrows/Tests/ArrowMonadInstances.v) and
[ArrowTransformerInstances.v](../../Taxonomy/Arrows/Tests/ArrowTransformerInstances.v)
check concrete carriers, dictionary reuse, and option/state stacks.
[Checks](../../Checks/CONTEXT.md) is the separate opt-in assumption audit.
