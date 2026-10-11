# Classes tests

Parent: [Classes context](../Lib/CONTEXT.md). Shared proof conventions:
[root CLAUDE.md](../../CLAUDE.md).

## Scope

[ArrowMonadRegression.v](ArrowMonadRegression.v) protects the generic
arrow-derived monad and its application-law contract. It imports
[Arrow.v](../Lib/Arrow/Arrow.v), [ArrowApplyFacts.v](../Lib/Arrow/ArrowApplyFacts.v),
[ArrowMonad.v](../Lib/Arrow/ArrowMonad.v), ITree's monad laws,
and Coq equality infrastructure, without importing Taxonomy carriers.

## What the regression establishes

- `CoreFactDependencies` checks `first_constant` and `pure_comp_ext` with
  core laws and explicit pure congruence, without application operations or
  laws. `StaticApplicationDependencies` checks constant application with
  only its fixed-arrow equation and core laws, without application laws.
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
[_CoqProject](../_CoqProject), so it belongs to the normal build.

[Taxonomy tests](CONTEXT-arrows.md) serve a different scope:
[ArrowMonadInstances.v](ArrowMonadInstances.v) and
[ArrowTransformerInstances.v](ArrowTransformerInstances.v)
check concrete carriers, dictionary reuse, and option/state stacks.
[Checks](../Checks/CONTEXT.md) is the separate opt-in assumption audit.
