(** * Paper claims index

    One block per section and contribution of the paper, in paper order.
    Each block names the paper location and the claim, then [Check]s the
    Rocq names that state it.  [PAPER.md] at the repository root is the
    evaluator-facing table built from this file; every Rocq name it mentions
    is checked here.  Assumptions are reported by [Checks/Assumptions.v].

    Modules are required without [Import] and names are qualified by file
    (and by [Module] where the file has one), so a [Check] fails if a name
    moves. *)

From Incorrectness.Lib.Monad Require
  OrderedMonad MonadRelation TransformerLaws.
From Incorrectness.Lib.Arrow Require
  ArrowMonad ArrowMorphism StateArrowT OptionArrowT.
From Incorrectness.Lib.Arrow.StateArrowT Require
  Core ArrowApplyLaws.
From Incorrectness.Lib.Arrow.OptionArrowT Require
  ArrowApplyLaws.
From Incorrectness.Verification.DivNonDet Require
  Computation.
From Incorrectness.Verification.DivNonDetSt Require
  Computation.
From Incorrectness.Verification.DivNonDetStExc Require
  Computation.
From Incorrectness.Relational Require
  PredMonad OptionLoop.
From Incorrectness.WP Require
  WPure WPVariants.
From Incorrectness.SP Require
  SPostMonad StatefulSPostCounterexample PredicateTransformerProperties
  SPostArr DSPASLPArr SPostArrEquiv ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.PTMonadTaxonomy Require
  TransformerRelations MonotoneSPSt SPStBindComparisons MonadTaxonomy.
From Incorrectness.Verification.Generic Require
  Triple.
From Incorrectness.Verification.DivNonDet Require
  Triples.
From Incorrectness.Verification.DivNonDetSt Require
  Triples.
From Incorrectness.Verification.DivNonDetStExc Require
  Triples.
From Incorrectness.Verification.DivNonDet Require
  Morphisms.
From Incorrectness.Verification.DivNonDetSt Require
  Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require
  Morphisms.
From Incorrectness.Verification.Generic Require
  Triple.
From Incorrectness.Verification.DivNonDet Require
  Triples.
From Incorrectness.Verification.DivNonDetSt Require
  Triples.
From Incorrectness.Verification.DivNonDetStExc Require
  Triples.
From Incorrectness.Verification.Generic Require
  TripleTaxonomy.
From Incorrectness.Verification.DivNonDet Require
  TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetSt Require
  TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetStExc Require
  TriplesTaxonomy TriplesExamples.
From Incorrectness.Verification.DivNonDetSt Require
  InCorrectnessPrinciples.
From Incorrectness.Verification.Generic Require
  DijkstraMonad.
From Incorrectness.Verification.DivNonDet Require
  DijkstraMonads.
From Incorrectness.Verification.DivNonDetSt Require
  DijkstraMonads.
From Incorrectness.Verification.DivNonDetStExc Require
  DijkstraMonads.
From Incorrectness.Verification.Generic Require
  Typings.
From Incorrectness.Verification.DivNonDet Require
  Typings.
From Incorrectness.Verification.DivNonDetSt Require
  Typings.
From Incorrectness.Verification.DivNonDetStExc Require
  Typings.
From Incorrectness.Verification.DivNonDet Require
  Typings.
From Incorrectness.Verification.DivNonDetStExc Require
  DijkstraExamples.
From Incorrectness.GaloisConnections Require
  BaseGaloisConnections GaloisArr.

(* ================================================================= *)
(** ** Section 1, Introduction                                       *)
(* ================================================================= *)

(** "monotone sps alone do not form a lawful monad": on monotone stateful
    forward transformers the angelic structure satisfies left unit only as
    an inequation, and the converse inequation fails for any inhabited
    state type. *)
Check MonotoneSPSt.SPStMonotone.AngelicMonotone.lunitStrictlyLax.

(** Bullet 3: "our base computation monad of nondeterminism and
    nontermination" (non-empty outcome sets, divergence an outcome). *)
Check Computation.divndNE.

(* ================================================================= *)
(** ** Section 2, Background: WP monads                              *)
(* ================================================================= *)

(** [WPure A = (A -> Prop) -> Prop], monotone, with the continuation
    [ret]/[bind]: a lawful monad, ordered with monotone [bind]; [WSt S]
    ([stateT] over it) and [WStExc S] ([stateT] over [optionT]) as well. *)
Check WPure.WPure.
Check WPure.MonadLawsE_WPure.
Check WPure.OrderedMonad_WPure.
Check WPure.OrderedMonad_WSt.
Check WPure.OrderedMonad_WStExc.

(* ================================================================= *)
(** ** Section 3.1, SPost: base sp monad                             *)
(* ================================================================= *)

(** Maillard et al.'s [SPost], carrier [(pre : Prop) -> A -> {p | p -> pre}]:
    a lawful monad, ordered.  [KenjiPureSP] is the same restriction
    (monotone + codomain) on raw [SPPure A = Prop -> A -> Prop]. *)
Check SPostMonad.SPM.SPost.
Check SPostMonad.SPMFacts.MonadLawsE_SPost.
Check SPostMonad.OrderedMonad_SPost.
Check SPostMonad.KenjiPureSP.

(* ================================================================= *)
(** ** Section 3.2, SPostArr: base sp arrow                          *)
(* ================================================================= *)

(** An arrow with application, input fixed, is a lawful monad; the state
    and option arrow transformers preserve the application laws. *)
Check ArrowMonad.MonadLawsE_Arrow.
Check StateArrowT.Core.stateArrT.
Check StateArrowT.ArrowApplyLaws.ArrowApplyLaws_stateArrT.
Check OptionArrowT.ArrowApplyLaws.ArrowApplyLaws_optionArrT.

(** The angelic arrow [ASPArr] (monotone, strict, disjunctive) and the
    demonic arrow [DSLPArr] (monotone, terminating, conjunctive) on
    [(B -> Prop) -> A -> Prop], with lawful application. *)
Check SPostArr.ASPArr.
Check SPostArr.ArrowApplyLaws_ASPArr.
Check SPostArr.DSLPArr.
Check SPostArr.ArrowApplyLaws_DSLPArr.

(** "a lawful monad that is exactly SPost_ang / SPost_dem": the arrow monads
    at input [unit] ([ASP], [DSLP]) are isomorphic, by monad morphisms both
    ways, to the direct monads on [SPPure] ([ASPSP], [DSLPSP]), whose carrier
    conditions are Maillard et al.'s and its demonic dual. *)
Check ASPMonad.ASP.
Check ASPMonad.ASPSP.
Check ASPMonad.kenji_iff_singleton.
Check ASPMonad.aspsp_to_asp_morphism.
Check ASPMonad.asp_to_aspsp_morphism.
Check DSLPMonad.DSLPSP.
Check DSLPMonad.kenjidslp_iff_msingleton.
Check DSLPMonad.dslpsp_to_dslp_morphism.
Check DSLPMonad.dslp_to_dslpsp_morphism.

(* ================================================================= *)
(** ** Section 3.3, Correcting stateful SPostArr                     *)
(* ================================================================= *)

(** Stateful transformers restricted only by monotonicity and the codomain
    condition: the unit laws hold, [bind] is not associative (the paper's
    [m], [f], [g] with two states).  Over [option (A * S)]; [StKenji] is the
    same over [A * S].  Angelic only. *)
Check StatefulSPostCounterexample.KenjiProgSP.
Check StatefulSPostCounterexample.KenjiProgSP_bind_ret_r.
Check StatefulSPostCounterexample.KenjiProgSP_bind_ret_l_kenji.
Check StatefulSPostCounterexample.KenjiFailingBind.ProgSP_bind_bind_fails.
Check StatefulSPostCounterexample.StKenji.KenjiFailingBind.KenjiProgSP_bind_bind_fails.

(* ================================================================= *)
(** ** Section 3.4, Stateful ASP and DSLP                            *)
(* ================================================================= *)

(** Universal disjunctivity = strict + non-empty disjunctive (and the
    conjunctive dual); as normal forms of the ASP / DSLP carriers. *)
Check PredicateTransformerProperties.strict_disjunctiveArr_full_join.
Check PredicateTransformerProperties.terminating_conjunctiveArr_full_meet.
Check SPostArr.asp_join_iff.
Check SPostArr.dslp_meet_iff.

(** "codomain condition <-> strictness": stateless only. *)
Check ASPMonad.strict_to_singleton.

(** [ASPSt S = stateArrT S ASPArr unit] and [DSLPSt S] are lawful monads. *)
Check ASPMonad.ASPSt.
Check ASPMonad.MonadLawsE_ASPSt.
Check DSLPMonad.MonadLawsE_DSLPSt.

(* ================================================================= *)
(** ** Section 3.5, Stateful DSP and ASLP                            *)
(* ================================================================= *)

(** DSP (strict, conjunctive) and ASLP (terminating, disjunctive) arrows;
    each element is the meet (resp. join) of an ASP part and a DSLP part
    ([aspOf] / [dslpOf] in the paper); the monads are lawful. *)
Check DSPASLPArr.DSPArr.
Check DSPASLPArr.dsp_hom_iff.
Check DSPASLPArr.dspRel.
Check DSPASLPArr.aspPartArr.
Check DSPASLPArr.dsp_split.
Check DSPASLPArr.ASLPArr.
Check DSPASLPArr.aslp_hom_iff.
Check DSPASLPArr.aslp_split.
Check DSPMonad.MonadLawsE_DSPSt.
Check ASLPMonad.MonadLawsE_ASLPSt.

(** The four healthiness classes are distinct. *)
Check DSPASLPArr.no_ASPArr_for_dsp.
Check DSPASLPArr.no_DSLPArr_for_aslp.

(** Without state DSP is ASP and ASLP is DSLP (identity maps, monad
    morphisms both ways). *)
Check DSPMonad.dsp_to_asp_morphism.
Check DSPMonad.asp_to_dsp_morphism.
Check ASLPMonad.aslp_to_dslp_morphism.
Check ASLPMonad.dslp_to_aslp_morphism.

(* ================================================================= *)
(** ** Section 3.6, WP monads of interpretations                     *)
(* ================================================================= *)

(** [bind] of [WPure] preserves each condition ([ret] satisfies all), so
    each restriction is a submonad of [WPure], ordered by pullback; both
    orders on the flavours, with state. *)
Check WPVariants.wpure_bind_strict.
Check WPVariants.wpure_bind_terminating.
Check WPVariants.wpure_bind_conjunctive.
Check WPVariants.wpure_bind_disjunctive.
Check WPVariants.OrderedMonad_WPSub.
Check OrderedMonad.OrderedMonad_SubMonad.
Check WPVariants.OrderedMonad_DWLPSt.
Check WPVariants.OrderedMonad_DWLPSt_op.

(* ================================================================= *)
(** ** Section 4, Taxonomy (Figure 1)                                *)
(* ================================================================= *)

(** 4.1: implication, contrapositive and Galois connection on bare
    monotone transformers. *)
Check TransformerRelations.pt_le.
Check TransformerRelations.Contrapositive.
Check TransformerRelations.GaloisPT.

(** 4.2: DM4All's monadic relation; an ordered monad's order is one. *)
Check MonadRelation.MonadRelation.
Check MonadRelation.MonadRelation_OrderedMonad.

(** Figure 1b implication edges, WP (state; each also has its converse). *)
Check MonadTaxonomy.MonadRelation_dwp_implies_dwlp.
Check MonadTaxonomy.MonadRelation_dwp_implies_awp.
Check MonadTaxonomy.MonadRelation_awp_implies_awlp.
Check MonadTaxonomy.MonadRelation_dwlp_implies_awlp.

(** Figure 1b implication edges, SP (state), through the ASP / DSLP part of
    DSP and ASLP (the asterisks); a relation through the part entails
    implication of the elements themselves. *)
Check MonadTaxonomy.MonadRelation_dsp_implies_asp.
Check MonadTaxonomy.MonadRelation_dsp_implies_dslp.
Check MonadTaxonomy.MonadRelation_asp_implies_aslp.
Check MonadTaxonomy.MonadRelation_dslp_implies_aslp.
Check MonadTaxonomy.dsp_implies_asp_part.
Check MonadTaxonomy.asp_implies_aslp_part.

(** Figure 1 contrapositive edges (state). *)
Check MonadTaxonomy.MonadRelation_contra_awp_dwlp_one.
Check MonadTaxonomy.MonadRelation_contra_dwp_awlp_one.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_one.
Check MonadTaxonomy.MonadRelation_contra_dsp_aslp_one.

(** Figure 1 Galois edges: ASP -| DWLP and AWP -| DSLP. *)
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp.
Check MonadTaxonomy.MonadRelation_galois_awp_dslp.

(** Figure 1a: the collapse without state. *)
Check MonadTaxonomy.MonadRelation_dsp_asp_pure.
Check MonadTaxonomy.MonadRelation_aslp_dslp_pure.

(** 4.4 effect-modularity.  WP edges are proved on [WPure] and lifted by
    [stateT] / [optionT]; SP edges are index-generic statements about
    denoted relations, so they hold at every arrow-transformer stack;
    Galois edges come from one [Pred] / [WPure] relation.  Instances
    without state and with state + exceptions. *)
Check MonadRelation.MonadRelation_stateT.
Check MonadRelation.MonadRelation_optionT.
Check MonadTaxonomy.MonadRelation_impliesWPure.
Check MonadTaxonomy.MonadRelation_implies_WPSubStExc.
Check MonadRelation.MonadRelation_rel_incl_state_option.
Check MonadTaxonomy.MonadRelation_GaloisPredWP.
Check MonadTaxonomy.MonadRelation_dsp_implies_asp_exc.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_pure.
Check MonadTaxonomy.MonadRelation_contra_asp_dslp_exc_one.
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp_pure.
Check MonadTaxonomy.MonadRelation_galois_asp_dwlp_exc.

(* ================================================================= *)
(** ** Section 5, Triples (contribution bullet 3)                    *)
(* ================================================================= *)

(** Monad morphisms and their lifts through [stateT] / [optionT]; arrow
    morphisms, their lifts through the arrow transformers, and the monad
    morphism of an arrow morphism; the triple of any monad morphism. *)
Check OrderedMonad.MonadMorphism.
Check TransformerLaws.MonadMorphism_stateT.
Check TransformerLaws.MonadMorphism_optionT.
Check ArrowMorphism.ArrowMorphism.
Check ArrowMorphism.state_option_arrow_morphism.
Check ArrowMorphism.arrow_morphism_monad.
Check Triple.triple.

(** The eight base morphisms out of [divndNE]: WP into [WPure]; SP into
    [ASP], [DSLP], [DSP], [ASLP]. *)
Check Morphisms.dwpPure_morphism.
Check Morphisms.dwlpPure_morphism.
Check Morphisms.awpPure_morphism.
Check Morphisms.awlpPure_morphism.
Check Morphisms.aspPure_morphism_rel.
Check Morphisms.dslpPure_morphism_rel.
Check Morphisms.dspPure_morphism_rel.
Check Morphisms.aslpPure_morphism_rel.

(** Lifted to state + exceptions; incorrectness logic [q => asp [[c]] p] is
    [triple aspSt c Under p q]. *)
Check Morphisms.dwpStExc_morphism.
Check Morphisms.aspStExc_morphism_rel.
Check Morphisms.dspStExc_morphism_rel.
Check Morphisms.aspSt.
Check Triples.triple_aspSt.

(** The taxonomy diagram on the triples of one stateful program (26 edges;
    again with exceptions, suffix [_exc]). *)
Check TriplesTaxonomy.TotalCorr_impl_PartCorr.
Check TriplesTaxonomy.DemIncorr_impl_IncorrLogic.
Check TriplesTaxonomy.LisbonLogic_contra_dwlp_over.
Check TriplesTaxonomy.IncorrLogic_contra_dslp_over.
Check TriplesTaxonomy.PartCorr_galois_asp_over.
Check TriplesTaxonomy.awp_over_galois_PartIncorr.

(** Verified programs: one per triple kind (16), and O'Hearn's Example 3.1. *)
Check ProgA.progA_dwp_under.
Check ProgA.progA_asp_under.
Check ProgEx.progEx_dslp_under.
Check OHearn.example_incorrect.

(* ================================================================= *)
(** ** Section 6, Dijkstra monads (contribution bullets 4 and 5)     *)
(* ================================================================= *)

(** Specification monads stay so with the order flipped.  ASP and DSLP are
    specification monads with state and with state + exceptions. *)
Check OrderedMonad.OrderedMonad_flip.
Check ASPMonad.OrderedMonad_ASPSt.
Check ASPMonad.OrderedMonad_ASPStExc.
Check DSLPMonad.OrderedMonad_DSLPSt.
Check DSLPMonad.OrderedMonad_DSLPStExc.

(** DSP and ASLP: with state, [bind] is not monotone for the natural order;
    no left-unital monotone [bind] exists.  Without state they are
    specification monads (they are ASP / DSLP). *)
Check DSPMonad.not_OrderedMonad_DSPSt.
Check ASLPMonad.not_OrderedMonad_ASLPSt.
Check DSPMonad.dsp_arbitrary_bind_impossible.
Check DSPMonad.OrderedMonad_DSP.

(** The Dijkstra monad of a monad morphism ([DM]; [DMop] for the flipped
    order) and DM4All's laws; eight WP and four SP instances. *)
Check DijkstraMonad.DM.
Check DijkstraMonad.DMop.
Check DijkstraMonad.DM_laws.
Check DijkstraMonads.Dasp_laws.

(** Triples are typings: every WP triple, ASP [Over], DSLP [Under]. *)
Check Typings.triple_under_wpStExc.
Check Typings.triple_over_wpStExc.
Check Typings.triple_over_aspStExc.
Check Typings.triple_under_dslpStExc.

(** ASP [Under] / DSLP [Over]: typing at the natural index demands that
    every start state in [P] reach every result in [Q], which implies the
    triple but not conversely; no index has the triple as its typings
    (with state); without state ASP [Under] is a typing. *)
Check Typings.le_aspUnder.
Check Typings.aspUnder_typing_triple.
Check Typings.no_asp_under_index.
Check Typings.no_dslp_over_index.
Check Triple.Under.
Check Typings.triple_under_aspPure.

(** Typed programs, a triple that is not a typing, the stateless case. *)
Check DijkstraExamples.progA_Ddwp.
Check DijkstraExamples.progA_Dasp.
Check DijkstraExamples.progEx_Ddslp_op.
Check DijkstraExamples.progloom_harder_not_Dasp_op.
Check MonadTaxonomy.impliesWPure.
(* Bullet 5 gap: strictness of the typing and the DSLP Over dual. *)
Check Withdrawal.progloom_harder_asp_under.
Check Typings.dslpOver_typing_triple.
Check DijkstraExamples.progloom_harder_dslp_over.
Check DijkstraExamples.progloom_harder_not_Ddslp.
Check Typings.oneOrTwo_Dasp_op.

(* ================================================================= *)
(** ** Section 7, Galois connections (contribution bullet 6)         *)
(* ================================================================= *)

(** DM4All's adjunctions between the base specification monads, including
    the second WP / PrePost one (classical). *)
Check PredMonad.OrderedMonad_Pred.
Check BaseGaloisConnections.pred_pp_adjunction.
Check BaseGaloisConnections.wp_pp_under_adjunction.
Check BaseGaloisConnections.wp_pp_over_adjunction.
Check BaseGaloisConnections.sp_pp_adjunction.

(** Nearest results to "Pred ~ SPost extends to asp and dslp" (no such
    isomorphism is stated): ASP and DSLP arrows are isomorphic to relations;
    an ASP arrow converts to the DSLP arrow of the same relation; relations
    and monotone SP transformers form a Galois connection. *)
Check SPostArrEquiv.asp_to_rel_morphism.
Check SPostArrEquiv.dslp_to_rel_morphism.
Check SPostArr.asp_to_dslp.
Check GaloisArr.Galois_Rel_SPost.

(* ================================================================= *)
(** ** The one admitted lemma (unused)                               *)
(* ================================================================= *)

Check MonotoneSPSt.SPStMonotone.DemonicMonotone.Radj_bind.

(* ================================================================= *)
(** ** Beyond the paper                                              *)
(* ================================================================= *)

(** No lawful [ArrowLoop] for option relations, nor for option ASP / DSLP
    arrows. *)
Check OptionLoop.optionRel_no_lawful_ArrowLoop.
Check SPostArrEquiv.optionASP_no_lawful_ArrowLoop.

(** O'Hearn's rewriting rules over [aspSt] triples. *)
Check InCorrectnessPrinciples.principle_of_denial_asp.
Check Morphisms.dwlpSt.

(** Galois connections between binary specification arrows. *)
Check GaloisArr.Galois_RPP_WP.

(** The stateful ASP [bind] is the angelic [bind] of monotone transformers. *)
Check SPStBindComparisons.bindASPSt_angelic.
