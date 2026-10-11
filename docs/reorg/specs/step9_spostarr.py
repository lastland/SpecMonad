SOURCE = "SP/SPostArr.v"
PARTS = [
    ("SP/SPostArr.v", """(** * Property-only strongest-postcondition arrows: ASP and DSLP
      (paper, Sections 3.2-3.4).

    The canonical carriers contain predicate transformers and healthiness
    proofs, not stored relations. ASP/DSLP have constructive normal forms.
    Compatibility names and binary transformer stacks share these
    definitions.  The DSP and ASLP arrows, built from these two, are in
    [DSPASLPArr.v]. *)
""", [(7, 1786)]),
    ("SP/DSPASLPArr.v", """(** * Property-only strongest-postcondition arrows: DSP and ASLP
      (paper, Section 3.5).

    DSP/ASLP recover relations classically and split operations into their
    ASP and DSLP readings, which they combine by conjunction / disjunction.
    The file ends with the separation of the four healthiness classes. *)

From Coq Require Import FunctionalExtensionality PropExtensionality RelationClasses
  Morphisms Setoid Classical_Prop.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Arrow Require Export ArrowMonad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT
  ArrowMorphism RelArrowCoherence.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Export PredicateTransformerProperties.
From Incorrectness.SP Require Import SPostArr.

Local Obligation Tactic := idtac.
""", [(1787, None)]),
]
BOTH = ["SP/SPostArr.v", "SP/DSPASLPArr.v"]
USES = {f: BOTH for f in [
    "SP/SPostArrEquiv.v", "SP/DSPMonad.v", "SP/ASLPMonad.v", "Tests/ArrowMonadInstances.v",
    "Tests/SPostArrInfrastructure.v", "Taxonomy/MonadTaxonomy.v", "Triples/MonadMorphisms.v",
    "Triples/Diagram.v", "Checks/Assumptions.v"]}
USES["*"] = ["SP/SPostArr.v"]
QUALIFIED = {"Checks/Assumptions.v": [
    (f"SPostArr.{n}.", f"DSPASLPArr.{n}.") for n in [
        "ArrowLaws_DSPArr", "ArrowChoiceLaws_DSPArr", "ArrowApplyLaws_DSPArr",
        "ArrowLaws_ASLPArr", "ArrowChoiceLaws_ASLPArr", "ArrowApplyLaws_ASLPArr",
        "no_ASPArr_for_dsp", "no_DSLPArr_for_dsp", "no_ASPArr_for_aslp",
        "no_DSLPArr_for_aslp", "no_ASPArr_for_dslp"]]}
DUPLICATED = ["Local Obligation Tactic := idtac."]
