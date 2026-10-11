import re
from pathlib import Path

SOURCE = "Verification/Triples/MonadMorphisms.v"
import subprocess
# The source as of the commit before this split (the file is gone afterwards).
_src = subprocess.run(["git", "show", "fcf37ca:Code/" + SOURCE], capture_output=True, text=True,
                      check=True, cwd=Path(__file__).resolve().parents[3]).stdout.splitlines(keepends=True)
_L = lambda a, b: "".join(_src[a - 1:b])
IMPORTS = _L(44, 63)
_head = _L(1, 26)
assert _head.rstrip().endswith("and their DSLP, DSP, ASLP counterparts.")

PARTS = [
    ("Verification/MonadMorphisms/MonadMorphisms.v", _head + """
    All twenty-four have an [IsMonadMorphism] instance.  They are the common
    ground of the paper's Sections 5 and 6: a triple is a morphism followed
    by a reading of the specification ([Triples/Triple.v]), and a Dijkstra
    monad indexes programs by their image under a morphism
    ([DijkstraMonads/DijkstraMonad.v]).  The triples of these morphisms, and
    how they lift through the transformers, are in
    [Triples/MorphismTriples.v].

    At the input [unit] of the base monads DSP coincides with ASP and ASLP
    with DSLP ([DSPMonad.v], [ASLPMonad.v]); what tells the four apart is
    the base arrow at an arbitrary input. *)

""" + IMPORTS,
     [(65, 204), (226, 258), (272, 300), (314, 342), (356, 384), (398, 927),
      (966, 1028), (1050, 1112), (1134, 1195), (1217, 1281)]),
    ("Verification/Triples/MorphismTriples.v", """(** * The triples of the monad morphisms, and how they lift

    Every morphism of [MonadMorphisms/MonadMorphisms.v] has its [triple]
    ([Triple.v]).  The triples lift with the morphisms:

      WP   the triple at a stack is the base triple, start state by start
           state ([triple_dwpSt] &c.);

      SP   the triples at the three levels are the judgement on one base
           arrow at three pairs of indices ([triple_aspPure],
           [triple_aspSt], [triple_aspStExc] &c.).  The arrow
           transformers change only the indices.

    An SP triple does not in general split start state by start state: an
    incorrectness triple at the state level asks for SOME start state per
    outcome.  The last part reads each of the twenty-four triples in terms
    of the outcomes of the program ([dwpSt_read] &c.). *)

""" + IMPORTS + """From Incorrectness.Verification.MonadMorphisms Require Import MonadMorphisms.
From Incorrectness.Verification.Triples Require Import Triple.

(** A base morphism into [WPure], under [stateT], and under [stateT] over
    [optionT]. *)
Section LiftedWP.
  Variable σ : forall A, divndNE A -> WPure A.
  Hypothesis Hσ :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure σ.
  Variable S : Type.
""",
     [(205, 226), (259, 271), (301, 313), (343, 355), (385, 397), (928, 965),
      (1029, 1049), (1113, 1133), (1196, 1216), (1282, None)]),
]

MORPH, TRIPLES = PARTS[0][0], PARTS[1][0]
BOTH = [MORPH, TRIPLES]
USES = {f: BOTH for f in ["Verification/Triples/TripleTaxonomy.v", "Verification/Triples/Examples.v",
                          "Checks/Assumptions.v", "Checks/PaperClaims.v"]}
USES["*"] = [MORPH]

# Names that move to MorphismTriples: qualified references must follow.
_triple_text = "".join(_L(a, b if b else len(_src)) for a, b in PARTS[1][2])
TRIPLE_NAMES = sorted(set(re.findall(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:Theorem|Lemma|Definition|Corollary)\s+([\w']+)", _triple_text, re.M)))
QUALIFIED = {}
for f in ["Checks/Assumptions.v", "Checks/PaperClaims.v"]:
    text = (Path(__file__).resolve().parents[3] / "Code" / f).read_text()
    QUALIFIED[f] = [(f"MonadMorphisms.{n}.", f"MorphismTriples.{n}.") for n in TRIPLE_NAMES
                    if f"MonadMorphisms.{n}." in text]
DUPLICATED = ["Section LiftedWP.", "Variable σ : forall A, divndNE A -> WPure A.", "Hypothesis Hσ :",
              "@MonadMorphism divndNE WPure Monad__divndNE Monad_WPure", "Eq1__divndNE Eq1_WPure σ.",
              "Variable S : Type.", "End LiftedWP."]
