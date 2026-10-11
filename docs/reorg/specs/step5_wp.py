SOURCE = "WP/WPureMonad.v"
IMPORTS = """From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
"""
PARTS = [
    ("WP/WPure.v", """(** * [WPure]: the monad of MONOTONE weakest-precondition transformers,
      and its two program-shaped stacks (paper, Section 2).

    This file contains exactly three developments:

      [WPure  A]      = { f : (A -> Prop) -> Prop | f is monotone }
      [WSt    S A]    = stateT S WPure A            (* W^St     *)
      [WStExc S A]    = stateT S (optionT WPure) A  (* W^StExc  *)

    Monotonicity is part of the carrier.  The adjunction proofs in
    [BaseGaloisConnections.v] and the [Proper_bind] proof below use it.

    The evaluators take an initial state and a postcondition on [A * S]
    for [WSt], or on [option (A * S)] for [WStExc].  The latter stack
    supplies [MonadExc].  These evaluator shapes omit the bundled
    monotonicity proofs and the transformer wrappers.

    The four WP variants carved out of [WPure] are in [WPVariants.v]. *)

""" + IMPORTS, [(26, 244)]),
    ("WP/WPVariants.v", """(** * The four WP variants [AWP], [DWLP], [DWP], [AWLP] (paper, Section 3.6).

    Each is [WPure] restricted by a healthiness condition that [ret] and
    [bind] preserve, so each is a submonad of [WPure] with the order pulled
    back from it. *)

""" + IMPORTS + "From Incorrectness.WP Require Import WPure.\n", [(245, None)]),
]
USES = {
    "Taxonomy/MonadTaxonomy.v": ["WP/WPure.v", "WP/WPVariants.v"],
    "*": ["WP/WPure.v"],
}
QUALIFIED = {"Checks/Assumptions.v": [
    ("WPureMonad.OrderedMonad_WPure.", "WPure.OrderedMonad_WPure."),
    ("WPureMonad.OrderedMonad_WSt.", "WPure.OrderedMonad_WSt."),
    ("WPureMonad.OrderedMonad_WStExc.", "WPure.OrderedMonad_WStExc."),
    ("WPureMonad.OrderedMonad_WPSub.", "WPVariants.OrderedMonad_WPSub."),
]}
DUPLICATED = []
