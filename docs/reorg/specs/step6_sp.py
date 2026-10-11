SOURCE = "SP/SPPredicateTransformers.v"
PARTS = [
    ("SP/RawSP.v", """(** * Raw strongest-postcondition transformers (paper, Section 3).

    [SPPure A = Prop -> A -> Prop], the stateful [SPSt] and [SPStExc], the
    terminating-slice variant [StTrans], and the refinement order on raw
    transformers with its monotonicity facts.  The four SP monads are not
    defined on these carriers: they come from the arrows of [SPostArr.v]. *)
""", [(1, 188)]),
    ("Taxonomy/MonotoneSPSt.v", """(** * Monotone stateful SP transformers [SPStMon] (paper, Introduction,
      Section 3.2 and Section 4).

    The angelic and demonic monad structures on monotone stateful forward
    transformers satisfy the unit laws only laxly ([lunitStrictlyLax]):
    monotone sps alone are not a lawful monad.  The file also proves the
    adjunctions [Ladj] / [Radj] between these transformers and [WSt], and
    their representability by [PredSt]; [MonadTaxonomy.v] uses them for the
    Galois edges of the taxonomy.  [Radj_bind] is [Admitted] and unused. *)

From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.
From Incorrectness.SP Require Import RawSP.

Import MonadNotation.
Open Scope monad_scope.
""", [(190, None)]),
]
BOTH = ["SP/RawSP.v", "Taxonomy/MonotoneSPSt.v"]
USES = {
    "Taxonomy/SPStBindComparisons.v": BOTH,
    "Taxonomy/MonadTaxonomy.v": BOTH,
    "*": ["SP/RawSP.v"],
}
QUALIFIED = {
    "Taxonomy/SPStBindComparisons.v": [("@SPPredicateTransformers.SPSt", "@RawSP.SPSt")],
    "Taxonomy/MonadTaxonomy.v": [
        ("Import SPPredicateTransformers.SPStMonotone.", "Import MonotoneSPSt.SPStMonotone."),
        ("[SPPredicateTransformers.v]", "[MonotoneSPSt.v]")],
    "SP/SPostMonad.v": [("[SPPredicateTransformers.v]", "[RawSP.v]")],
}
DUPLICATED = ["Import MonadNotation.", "Open Scope monad_scope."]
