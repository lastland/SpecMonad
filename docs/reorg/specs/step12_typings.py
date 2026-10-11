import re
import subprocess
from pathlib import Path

SOURCE = "Verification/DijkstraMonads/DijkstraMonad.v"
_src = subprocess.run(["git", "show", "7f918d6:Code/" + SOURCE], capture_output=True, text=True,
                      check=True, cwd=Path(__file__).resolve().parents[3]).stdout.splitlines(keepends=True)
_find = lambda pred: next(i for i, l in enumerate(_src, 1) if pred(l))
_imp0 = _find(lambda l: l.startswith("From Coq Require"))
_triple = _find(lambda l: "Verification.Triples Require Import Triple" in l)
_mm = _find(lambda l: "Verification.MonadMorphisms Require Import MonadMorphisms" in l)
_cut = _find(lambda l: l.startswith("(** * Triples are typings")) - 1   # the banner's first line
_par = _find(lambda l: l.startswith("    Triples are typings where the two say the same"))
assert _triple + 1 == _mm and _src[_cut - 1].startswith("(* ====")
_L = lambda a, b: "".join(_src[a - 1:b])
IMPORTS = _L(_imp0, _triple - 1) + _L(_mm, _mm)

PARTS = [
    (SOURCE, _L(1, _par - 1).rstrip() + """

    How triples relate to these typings -- which triples are typings and
    which are not -- is in [TriplesAsTypings/TriplesAsTypings.v]. *)

""" + IMPORTS, [(_mm + 1, _cut - 1)]),
    ("Verification/TriplesAsTypings/TriplesAsTypings.v", """(** * Triples as typings in the Dijkstra monads (paper, Section 6)

    The Dijkstra monads of [DijkstraMonads/DijkstraMonad.v] and the triples
    of [Triples/] are both read off the same monad morphisms; this file
    compares them.
""" + _L(_par - 1, _imp0 - 1) + _L(_imp0, _mm) + """From Incorrectness.Verification.DijkstraMonads Require Import DijkstraMonad.
""", [(_cut, None)]),
]
BASE, CMP = PARTS[0][0], PARTS[1][0]
USES = {"Verification/DijkstraMonads/DijkstraExamples.v": [BASE, CMP],
        "Checks/Assumptions.v": [BASE, CMP], "Checks/PaperClaims.v": [BASE, CMP], "*": [BASE]}
_cmp_text = _L(_cut, len(_src))
CMP_NAMES = sorted(set(re.findall(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:Theorem|Lemma|Definition|Corollary|Instance|Example)\s+([\w']+)", _cmp_text, re.M)))
QUALIFIED = {}
for f in ["Checks/Assumptions.v", "Checks/PaperClaims.v"]:
    text = (Path(__file__).resolve().parents[3] / "Code" / f).read_text()
    QUALIFIED[f] = [(f"DijkstraMonad.{n}.", f"TriplesAsTypings.{n}.") for n in CMP_NAMES
                    if f"DijkstraMonad.{n}." in text]
DUPLICATED = []
