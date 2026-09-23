# SP observations context (main)

Parent: [effect observations](../CONTEXT.md).
Targets: [base specifications](../../BaseSpecMonads/CONTEXT.md).
Related: [WP observations](../WP/CONTEXT.md).

## Purpose and scope

The five hand-written files below define strongest-postcondition observations into healthy
base-monad values, return/bind preservation, and triples. The relation-derived
files are described under [From a relation](#from-a-relation). The stateful taxonomy belongs
to the parent directory; pure/reader collapse results stay with their observations.

## Choose the outcome indexing first

| Source file | Computation | Specification outcomes / module |
|---|---|---|
| [StDivExcNonDet_SPStExc.v](StDivExcNonDet_SPStExc.v) | `stdivexcnd` | `option (A * S)`, terminating slice including exceptions; top level. |
| [StDivNonDet_SPStExc.v](StDivNonDet_SPStExc.v) | `stdivnd` | `option (A * S)`, including divergence; `FullOutcomeObs`. |
| [StDivNonDet_SPSt.v](StDivNonDet_SPSt.v) | `stdivnd` | `A * S`, normal returns only; `TermSliceObs`. |
| [DivNonDet_SPPure.v](DivNonDet_SPPure.v) | `divnd` | `A`, normal returns only; `PureObs`. |
| [RdDivNonDet_RdSPPure.v](RdDivNonDet_RdSPPure.v) | `rddivnd` | `A` at each environment; `RdPureObs`. |

The first two target `ASPStExc`, `DSLPStExc`, `DSPStExc`, and `ASLPStExc`.
`TermSliceObs` uses `StASP.ASPSt`, `StDSLP.DSLPSt`, `StDSP.DSPSt`, and
`StASLP.ASLPSt`; pure and reader files use the corresponding `ASPSP` /
`DSLPSP` / `DSPSP` / `ASLPSP` and `ASPRd` / `DSLPRd` / `DSPRd` / `ASLPRd`.
These SP sources are unrestricted computations, not the non-empty fragments.

## Readings and preservation

For the selected stateful relation `R s r`, **ASP** (angelic SP) reads
`exists s, pre s /\ R s r`; **DSLP** (demonic liberal SP) reads
`forall s, R s r -> pre s`. **DSP** (demonic SP) conjoins these readings;
**ASLP** (angelic liberal SP) disjoins them.
`obsASP`, `obsDSLP`, `obsDSP`, and `obsASLP` package the respective readings.

The stateful files prove local `outcomes_bind` facts, then `obs*_ret` and
`obs*_bind` for their actual target binds. DSP/ASLP proofs use relation recovery
from [DSPMonad.v](../../BaseSpecMonads/DSPMonad.v) and
[ASLPMonad.v](../../BaseSpecMonads/ASLPMonad.v); the target bind is not simple
forward composition. `RdPureObs` applies `PureObs` environment by environment.

## Semantic cautions

- The double-option file reads `unOptionT (unOptionT (runStateT m s)) (Some r)`.
  Outer divergence is omitted; `r = None` is a terminating exception.
- `FullOutcomeObs` instead reads `unOptionT (runStateT m s) r` directly.
  Its ASP at `None` means some `pre`-state may diverge; its DSLP at `None`
  means every state that may diverge satisfies `pre`.
- `TermSliceObs` reads at `Some r` with `r : A * S`, discarding divergence.
  A divergent-only computation has ASP/DSP false and DSLP/ASLP true on this
  slice. Thus ASP `Over` is vacuous there, but DSLP `Over` is not generally so.
- `PureObs.obsDSP_is_obsASP` and `PureObs.obsASLP_is_obsDSLP` record the pure
  collapse. The reader lift inherits it; its precondition is one `Prop` per
  environment, not a shared transformer input of type `R -> Prop`, even though
  its triples accept `pre : R -> Prop` and evaluate it at each environment.
- Determinism does not imply unique predecessors. Deterministic WP collapse
  does not justify identifying ASP with DSLP.

## Triples, orders, and boundaries

`Over` requires the observed postcondition to imply `post`; `Under` reverses
that implication. Raw `*spec` comparisons use plain `pp2_over` / `pp2_under`
transformers. They are distinct from the healthy in-monad targets in
[NewGaloisConnections.v](../../BaseSpecMonads/NewGaloisConnections.v): ASP
`Under` uses an `At` order and `exists s, pre s`; DSLP `Over` uses an `At`
order and `exists s, ~ pre s`. Do not erase those conditions.

Base healthiness and operations remain in the specification layer. Main's
double-option SP file nevertheless imports WP and arrow modules; the two
stateful single-option files show a smaller source/target import boundary.

## From a relation

The `_Rel` files observe into the arrow monads of
[BaseSpecMonads](../../BaseSpecMonads/CONTEXT.md) (`ASPMonad.v`, `DSLPMonad.v`,
`DSPMonad.v`, `ASLPMonad.v`), not the `OldMonads/` carriers the files above use.
Each supplies only the relation a computation denotes and its `ret` / `bind`
laws, as an instance of `PureRel`, `StRel` or `StExcRel` from
[SPRelDenote.v](../../BaseSpecMonads/SPRelDenote.v); all four observations and
their morphism laws are then citations. They are the SP counterpart of the WP
`_Algebra` files.

| Source | Computation | Interface |
|---|---|---|
| [DivNonDet_SPure_Rel.v](DivNonDet_SPure_Rel.v) | `divnd` | `PureRel`; outcomes `A` |
| [RdDivNonDet_RdSP_Rel.v](RdDivNonDet_RdSP_Rel.v) | `rddivnd` | `PureRel` environment by environment |
| [StDivNonDet_SPSt_Rel.v](StDivNonDet_SPSt_Rel.v) | `stdivnd` | `StRel`; terminating slice `A * S` |
| [StDivExcNonDet_SPStExc_Rel.v](StDivExcNonDet_SPStExc_Rel.v) | `stdivexcnd` | `StExcRel`; `option (A * S)`, divergence (`spinP`) dropped |

The `_Tower` files go one step further for ASP and DSLP: the relation and its
two laws are themselves DERIVED by stacking `optionT` / `stateT` steps over
`SetM` ([SPRelTower.v](../../BaseSpecMonads/SPRelTower.v)), and each proves its
observations definitionally equal to the matching `_Rel` ones.

## Reading order

Read the computation and selected relation, then the target bind and preservation
proof. Finish with the local triple definition and the matching
[comparison](../CONTEXT.md). Use [InCorrectnessPrinciples.v](../../InCorrectnessPrinciples.v)
for rules over the double-option ASP triples.
