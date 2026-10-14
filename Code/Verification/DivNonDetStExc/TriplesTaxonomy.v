(** * The taxonomy diagram, with state and exceptions

    The edges of [DivNonDetSt/TriplesTaxonomy.v] for [m : stdivexcndNE S A], under
    the same names with [_exc]; the base lemmas are used at the result type
    [option (A * S)]. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.WP Require Import
  WPure.

From Incorrectness.PTMonadTaxonomy Require Import
  MonadTaxonomy.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import TripleTaxonomy.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.

(** The same under [stateT] over [optionT]. *)
Section LiftedEdgesExc.
  Context {S : Type} (σ1 σ2 : forall A, divndNE A -> WPure A).

  Lemma wpStExc_under_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivexcndNE S A) (b : S -> Prop) (c : option (A * S) -> Prop),
      spec_holds (stateT_map S (optionT_map σ1) A m : WStExc S A) Under b c ->
      spec_holds (stateT_map S (optionT_map σ2) A m : WStExc S A) Under b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpStExc σ2 S m Under b c)). intro s.
    exact (pt_holds_incl_under _ _ _ _ (Hi _ (unOptionT (runStateT m s)))
             (proj1 (spec_holds_wpStExc σ1 S m Under b c) H s)).
  Qed.

  Lemma wpStExc_over_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivexcndNE S A) (b : S -> Prop) (c : option (A * S) -> Prop),
      spec_holds (stateT_map S (optionT_map σ2) A m : WStExc S A) Over b c ->
      spec_holds (stateT_map S (optionT_map σ1) A m : WStExc S A) Over b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpStExc σ1 S m Over b c)). intro s.
    exact (pt_holds_incl_over _ _ _ _ (Hi _ (unOptionT (runStateT m s)))
             (proj1 (spec_holds_wpStExc σ2 S m Over b c) H s)).
  Qed.

  Lemma wpStExc_contra :
    (forall X (d : divndNE X),
        pt_contra (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivexcndNE S A) (b : S -> Prop) (c : option (A * S) -> Prop),
      spec_holds (stateT_map S (optionT_map σ1) A m : WStExc S A) Under b c
      <-> spec_holds (stateT_map S (optionT_map σ2) A m : WStExc S A) Over
            (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    intros Hc A m b c.
    etransitivity; [ exact (spec_holds_wpStExc σ1 S m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (spec_holds_wpStExc σ2 S m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    split; intros H s.
    - exact (proj1 (pt_holds_contra _ _ _ _ (Hc _ (unOptionT (runStateT m s)))) (H s)).
    - exact (proj2 (pt_holds_contra _ _ _ _ (Hc _ (unOptionT (runStateT m s)))) (H s)).
  Qed.
End LiftedEdgesExc.

(* ================================================================= *)
(** * The diagram, with exceptions                                    *)
(* ================================================================= *)

(** The same twenty-six edges for one [m : stdivexcndNE S A], with a
    postcondition on [option (A * S)]: [None] is the exception.  The base
    lemmas are used at the result type [option (A * S)], and the SP edges
    at the output index [option (A * S)]; nothing else changes. *)

Section DiagramExc.
  Context {S A : Type} (m : stdivexcndNE S A)
    (b : S -> Prop) (c : option (A * S) -> Prop).

  Local Notation R :=
    (fun (us : unit * S) (o : option (A * S)) => outStExc m (snd us) (Some o)).

  (** ** WP implications *)

  Theorem TotalCorr_impl_PartCorr_exc :
    TotalCorr b m c -> PartCorr b m c.
  Proof.
    exact (wpStExc_under_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem LisbonLogic_impl_AngPartCorr_exc :
    LisbonLogic b m c -> AngPartCorr b m c.
  Proof.
    exact (wpStExc_under_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem TotalCorr_impl_LisbonLogic_exc :
    TotalCorr b m c -> LisbonLogic b m c.
  Proof.
    exact (wpStExc_under_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem PartCorr_impl_AngPartCorr_exc :
    PartCorr b m c -> AngPartCorr b m c.
  Proof.
    exact (wpStExc_under_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_over_impl_dwp_over_exc :
    triple (@dwlpStExc S) m Over b c -> triple (@dwpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_over_impl_awp_over_exc :
    triple (@awlpStExc S) m Over b c -> triple (@awpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem awp_over_impl_dwp_over_exc :
    triple (@awpStExc S) m Over b c -> triple (@dwpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem awlp_over_impl_dwlp_over_exc :
    triple (@awlpStExc S) m Over b c -> triple (@dwlpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  (** ** WP contrapositives *)

  Theorem LisbonLogic_contra_dwlp_over_exc :
    LisbonLogic b m c
    <-> triple (@dwlpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@awpPure) (@dwlpPure)
             (fun X d => awpPure_contra_dwlpPure d) A m b c).
  Qed.

  Theorem AngPartCorr_contra_dwp_over_exc :
    AngPartCorr b m c
    <-> triple (@dwpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@awlpPure) (@dwpPure)
             (fun X d => awlpPure_contra_dwpPure d) A m b c).
  Qed.

  Theorem TotalCorr_contra_awlp_over_exc :
    TotalCorr b m c
    <-> triple (@awlpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@dwpPure) (@awlpPure)
             (fun X d => dwpPure_contra_awlpPure d) A m b c).
  Qed.

  Theorem PartCorr_contra_awp_over_exc :
    PartCorr b m c
    <-> triple (@awpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@dwlpPure) (@awpPure)
             (fun X d => dwlpPure_contra_awpPure d) A m b c).
  Qed.

  (** ** SP implications *)

  Theorem aslp_over_impl_asp_over_exc :
    triple (@aslpStExc S) m Over b c -> triple (@aspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_aspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aslpStExc m Over b c) H)).
  Qed.

  Theorem aslp_over_impl_dslp_over_exc :
    triple (@aslpStExc S) m Over b c -> triple (@dslpStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dslpStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_aslpStExc m Over b c) H)).
  Qed.

  Theorem asp_over_impl_dsp_over_exc :
    triple (@aspStExc S) m Over b c -> triple (@dspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_aspStExc m Over b c) H)).
  Qed.

  Theorem dslp_over_impl_dsp_over_exc :
    triple (@dslpStExc S) m Over b c -> triple (@dspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dslpStExc m Over b c) H)).
  Qed.

  Theorem DemIncorr_impl_PartIncorr_exc :
    DemIncorr b m c -> PartIncorr b m c.
  Proof.
    intro H. apply (proj2 (triple_dslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dspStExc m Under b c) H)).
  Qed.

  Theorem DemIncorr_impl_IncorrLogic_exc :
    DemIncorr b m c -> IncorrLogic b m c.
  Proof.
    intro H. apply (proj2 (triple_aspStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_dspStExc m Under b c) H)).
  Qed.

  Theorem PartIncorr_impl_AngPartIncorr_exc :
    PartIncorr b m c -> AngPartIncorr b m c.
  Proof.
    intro H. apply (proj2 (triple_aslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_dslpStExc m Under b c) H)).
  Qed.

  Theorem IncorrLogic_impl_AngPartIncorr_exc :
    IncorrLogic b m c -> AngPartIncorr b m c.
  Proof.
    intro H. apply (proj2 (triple_aslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aspStExc m Under b c) H)).
  Qed.

  (** ** SP contrapositives *)

  Theorem DemIncorr_contra_aslp_over_exc :
    DemIncorr b m c
    <-> triple (@aslpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dspStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aslpStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dsp_contra_aslp R)).
  Qed.

  Theorem PartIncorr_contra_asp_over_exc :
    PartIncorr b m c
    <-> triple (@aspStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dslpStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aspStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dslp_contra_asp R)).
  Qed.

  Theorem IncorrLogic_contra_dslp_over_exc :
    IncorrLogic b m c
    <-> triple (@dslpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aspStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dslpStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (asp_contra_dslp R)).
  Qed.

  Theorem AngPartIncorr_contra_dsp_over_exc :
    AngPartIncorr b m c
    <-> triple (@dspStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aslpStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dspStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (aslp_contra_dsp R)).
  Qed.

  (** ** Galois connections *)

  Theorem PartCorr_galois_asp_over_exc :
    PartCorr b m c <-> triple (@aspStExc S) m Over b c.
  Proof.
    symmetry.
    refine (proj2 (galois_asp_rel (aspStExc m)
                     (fun s Q => getWPure (unOptionT (runStateT (dwlpStExc m) s)) Q)) _ b c).
    intros s Q.
    etransitivity; [ exact (galois_slice_dwlpPure (unOptionT (runStateT m s)) Q) |].
    split.
    - intros H y Hy. exact (H y (proj1 (aspRel_ofRel _ (tt, s) y) Hy)).
    - intros H a Ha. exact (H a (proj2 (aspRel_ofRel _ (tt, s) a) Ha)).
  Qed.

  Theorem awp_over_galois_PartIncorr_exc :
    triple (@awpStExc S) m Over b c <-> PartIncorr b m c.
  Proof.
    refine (proj2 (galois_dslp_rel
                     (fun s Q => getWPure (unOptionT (runStateT (awpStExc m) s)) Q)
                     (dslpStExc m)) _ c b).
    intros s Q.
    etransitivity; [ exact (galois_awpPure_slice (unOptionT (runStateT m s)) Q) |].
    split.
    - intros [a [Ha Hq]]. exists a.
      exact (conj (proj2 (dslpRel_ofRel _ (tt, s) a) Ha) Hq).
    - intros [y [Hy Hq]]. exists y.
      exact (conj (proj1 (dslpRel_ofRel _ (tt, s) y) Hy) Hq).
  Qed.
End DiagramExc.
