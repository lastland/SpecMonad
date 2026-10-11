SOURCE = "GaloisConnections/GaloisArr.v"
PARTS = [
    ("Taxonomy/TransformerTaxonomy.v", """(** * The taxonomy on bare predicate transformers (paper, Section 4.1).

    The monotone carrier [MonotoneSPost] read with either index fixed, as
    [MonoPT], and the three relations of Verscht and Kaminski's taxonomy on
    it: implication ([pt_le]), [Contrapositive] and [GaloisPT], with the two
    triples [pt_under] / [pt_over] of a transformer.  [MonadTaxonomy.v] lifts
    these relations to the monads. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions Classical_Prop.

From Incorrectness.SP Require Import SPostArr.

""", [(75, 87), (109, 118), (392, None)]),
    ("GaloisConnections/GaloisArr.v", '(** * Galois connections among the binary specification arrows.\n\n    Following Figure 1 of "Dijkstra Monads for All"\n    (Maillard et al., ICFP 2019), adapted from unary\n    specification monads to binary arrows.  Each Galois connection is\n    stated with the DM4all refinement orders:\n\n    - [Rel_le]: covariant inclusion on relations.\n    - [PrePost_le]: Hoare order (strengthen pre, weaken post).\n    - [WPArr_le]: DM4all refinement — reverse pointwise implication.\n      [w1 ≤ w2] iff [w2 a Q → w1 a Q] for all [a], [Q].\n    - [RelPrePost_le]: reverse pointwise implication on validators.\n\n    Four Galois connections are established:\n\n    1. [Galois_Rel_PrePost] — [α R := (True, R)], [γ pq := snd pq].\n       Embeds [Rel] as the full-pre fragment of [PrePostArr].\n\n    2. [Galois_Rel_SPost] — [α R := asp R], [γ sp := asp_inv sp].\n       Relates relations to monotone SP transformers.  Recovering a\n       relation after [asp] gives it back; the opposite round trip is\n       not an identity on all monotone transformers.\n\n    3. [Galois_WP_PrePost] — demonic WP concretization paired with\n       abstraction by [w a True] and the intersection of accepted\n       postconditions.  Requires [MonotoneWP].\n\n    4. [Galois_RPP_WP] — relates [MonotoneWP] to [WFRelPrePost].\n       The validator\'s well-formedness ensures that its projection [γ]\n       lands in [MonotoneWP].\n\n    A further section proves that one proposed binary SP/validator map,\n    [gamma_uni], is not monotone.  A second, existential proposal is\n    recorded as historical discussion, not as a proved counterexample.\n\n    These connections are not stated in the paper, whose Section 7 works\n    with unary specification monads ([BaseGaloisConnections.v]).  The\n    monotone carrier [MonotoneSPost] and its order are defined in\n    [Taxonomy/TransformerTaxonomy.v], which reads it as [MonoPT]. *)\n\nFrom Coq Require Import Morphisms RelationClasses Relation_Definitions Classical_Prop.\n\nFrom Incorrectness.Lib Require Import Galois.\nFrom Incorrectness.Relational Require Import RelSPostArr Rel.\nFrom Incorrectness.GaloisConnections Require Import PrePostArr WPArr RelPrePostArr.\n' + "From Incorrectness.Taxonomy Require Import TransformerTaxonomy.\n", [(46, 74), (88, 108), (119, 391)]),
]
USES = {
    "Checks/Assumptions.v": ["Taxonomy/TransformerTaxonomy.v", "GaloisConnections/GaloisArr.v"],
    "*": ["Taxonomy/TransformerTaxonomy.v"],
}
QUALIFIED = {
    "Taxonomy/MonadTaxonomy.v": [
        ("GaloisArr.MonotoneSPost_le", "TransformerTaxonomy.MonotoneSPost_le"),
        ("GaloisArr.MonotoneSPost A B", "TransformerTaxonomy.MonotoneSPost A B"),
        ("[Arrows/GaloisArr.v]", "[TransformerTaxonomy.v]"),
        ("[GaloisArr.v]", "[TransformerTaxonomy.v]")],
    "Lib/Galois.v": [("[Taxonomy/Arrows/GaloisArr.v]", "[GaloisConnections/GaloisArr.v]")],
}
DUPLICATED = []
