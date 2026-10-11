SOURCE = "SP/SPostMonad.v"
PARTS = [
    ("SP/SPostMonad.v", "", [(1, 243), (398, 405)]),
    ("SP/StatefulSPostCounterexample.v", """(** * The stateful extension of [SPost] is not a monad (paper, Section 3.3).

    [KenjiProgSP] (over [option (A * S)]) and [StKenji.KenjiProgSP] (its
    terminating-slice twin over [A * S]) restrict stateful forward
    transformers by monotonicity and the codomain condition, the conditions
    under which [SPost] is a monad.  [KenjiFailingBind] and
    [StKenji.KenjiFailingBind] build the transformers [m], [f], [g] of the
    paper and show that the proposed [bind] is not associative.  The paper
    phrases this for [stateArrT] over the angelic SP arrow at input [unit];
    these are hand-built carriers of the same shape. *)

From ITree Require Import Basics.Monad.
From Coq Require Import RelationClasses.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.SP Require Import RawSP SPostMonad.
""", [(244, 397), (406, None)]),
]
USES = {"*": ["SP/SPostMonad.v"]}
QUALIFIED = {}
DUPLICATED = []
