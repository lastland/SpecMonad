# The Rocq development

Mechanization of *A Taxonomy of Predicate Transformer Monads for Specifying
Monadic Programs*. Directories follow the paper; [PAPER.md](../PAPER.md) maps
each claim to its Rocq name, and [Checks/PaperClaims.v](Checks/PaperClaims.v)
checks those names when `make check` runs.

## Build

Rocq/Coq 8.20 with `coq-ext-lib`, `coq-itree` and `coq-hammer-tactics`
(exact constraints: [coq-spec-monad.opam](coq-spec-monad.opam)).

```sh
make -j8        # the development (about 35 s on 8 cores)
make check      # assumption audit (Checks/Assumptions.v) and the claims index
make layers     # check that imports respect the directory layers
```

`make check` reports the axioms each selected theorem uses: functional and
propositional extensionality and, where stated, excluded middle
(`Classical_Prop.classic`).

## Layout, in paper order

| Directory | Paper | Contents |
|---|---|---|
| [Lib/](Lib/CONTEXT.md) | background | arrows with application and choice, the option/state arrow transformers, arrow morphisms, the monad of an arrow at a fixed input; ordered monads, monad morphisms, monadic relations, monad-transformer laws |
| [Computation/](Computation/CONTEXT.md) | §1, §5 | `divndNE`, nondeterminism and nontermination, with state and with state and exceptions |
| [Relational/](Relational/CONTEXT.md) | — | proof infrastructure: relations as arrows, the four SP readings of a relation, the predicate monad `Pred` |
| [WP/](WP/CONTEXT.md) | §2, §3.6 | `WPure` and its stacks; the WP variants AWP, DWLP, DWP, AWLP |
| [SP/](SP/CONTEXT.md) | §3.1–3.5 | `SPost` and why its stateful extension fails; the SP arrows ASP, DSLP, DSP, ASLP; the four SP monads |
| [Taxonomy/](Taxonomy/CONTEXT.md) | §4 | the taxonomy on bare transformers, then as monadic relations between the monads (Figure 1) |
| [Triples/](Triples/CONTEXT.md) | §5 | monad morphisms out of `divndNE`, the general triple, the triple diagram, examples |
| [Dijkstra/](Dijkstra/CONTEXT.md) | §6 | Dijkstra monads of the morphisms; which triples are typings |
| [GaloisConnections/](GaloisConnections/CONTEXT.md) | §7 | the DM4All specification monads and their adjunctions |
| [Tests/](Tests/CONTEXT.md) | — | regression and instance checks |
| [Checks/](Checks/CONTEXT.md) | — | opt-in audits: assumptions and the paper claims |

```mermaid
flowchart RL
  Computation[Computation] -->|1| Lib[Lib]
  Dijkstra[Dijkstra] -->|5| Triples[Triples]
  GaloisConnections[GaloisConnections] -->|1| Taxonomy[Taxonomy]
  Relational[Relational] -->|16| Lib[Lib]
  SP[SP] -->|11| Relational[Relational]
  Taxonomy[Taxonomy] -->|21| SP[SP]
  Taxonomy[Taxonomy] -->|5| WP[WP]
  Tests[Tests] -->|2| GaloisConnections[GaloisConnections]
  Triples[Triples] -->|4| Computation[Computation]
  Triples[Triples] -->|3| Taxonomy[Taxonomy]
  WP[WP] -->|4| Lib[Lib]
```

Edges implied by others are omitted; a label counts the imports along that
edge (`python3 scripts/depgraph.py --mermaid` regenerates this). Each
directory imports only from the ones it reaches
([scripts/layers.txt](scripts/layers.txt)); `make layers` and CI check it.
`python3 scripts/depgraph.py` writes `depgraph.html`, an interactive
file-level graph with a directory-only view.

## Where to start reading

1. [WP/WPure.v](WP/WPure.v), the familiar WP monad.
2. [SP/SPostMonad.v](SP/SPostMonad.v) and
   [SP/StatefulSPostCounterexample.v](SP/StatefulSPostCounterexample.v):
   the SP monad and why state breaks it.
3. [SP/SPostArr.v](SP/SPostArr.v), [SP/DSPASLPArr.v](SP/DSPASLPArr.v), then
   [SP/ASPMonad.v](SP/ASPMonad.v) and its three siblings.
4. [Taxonomy/TransformerTaxonomy.v](Taxonomy/TransformerTaxonomy.v), then
   `Section Flavours` of [Taxonomy/MonadTaxonomy.v](Taxonomy/MonadTaxonomy.v).
5. [Triples/MonadMorphisms.v](Triples/MonadMorphisms.v) and
   [Triples/Examples.v](Triples/Examples.v);
   [Dijkstra/DijkstraMonad.v](Dijkstra/DijkstraMonad.v).

The [design notes](../docs/design.md) tell the longer story;
`Backup/` and `ITreeExamples/` are outside the build.
