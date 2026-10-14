(** * The taxonomy diagram, with state

    For one computation [m : stdivndNE S A], read in the eight ways of
    [Morphisms.v], the sixteen triples stand in the relations of Verscht
    and Kaminski's diagram (POPL 2025, Figure 10): sixteen implications
    ([TotalCorr_impl_PartCorr] &c.), eight contrapositives
    ([LisbonLogic_contra_dwlp_over] &c., classical) and two Galois connections
    ([PartCorr_galois_asp_over], [awp_over_galois_PartIncorr]).  The WP
    edges are the base edges of [DivNonDet/TriplesTaxonomy.v] carried start
    state by start state; the SP edges are those of one relation
    ([Generic/TripleTaxonomy.v]).  [Under] triples are written by the names
    of their logics ([Triples.v]); [Over] triples are their contrapositives. *)

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
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Triples.

(** A relation between the base morphisms is one between their lifts,
    start state by start state. *)
Section LiftedEdges.
  Context {S : Type} (σ1 σ2 : forall A, divndNE A -> WPure A).

  Lemma wpSt_under_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop),
      spec_holds (stateT_map S σ1 A m : WSt S A) Under b c ->
      spec_holds (stateT_map S σ2 A m : WSt S A) Under b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpSt σ2 S m Under b c)). intro s.
    exact (pt_holds_incl_under _ _ _ _ (Hi _ (runStateT m s))
             (proj1 (spec_holds_wpSt σ1 S m Under b c) H s)).
  Qed.

  Lemma wpSt_over_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop),
      spec_holds (stateT_map S σ2 A m : WSt S A) Over b c ->
      spec_holds (stateT_map S σ1 A m : WSt S A) Over b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpSt σ1 S m Over b c)). intro s.
    exact (pt_holds_incl_over _ _ _ _ (Hi _ (runStateT m s))
             (proj1 (spec_holds_wpSt σ2 S m Over b c) H s)).
  Qed.

  Lemma wpSt_contra :
    (forall X (d : divndNE X),
        pt_contra (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop),
      spec_holds (stateT_map S σ1 A m : WSt S A) Under b c
      <-> spec_holds (stateT_map S σ2 A m : WSt S A) Over
            (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    intros Hc A m b c.
    etransitivity; [ exact (spec_holds_wpSt σ1 S m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (spec_holds_wpSt σ2 S m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    split; intros H s.
    - exact (proj1 (pt_holds_contra _ _ _ _ (Hc _ (runStateT m s))) (H s)).
    - exact (proj2 (pt_holds_contra _ _ _ _ (Hc _ (runStateT m s))) (H s)).
  Qed.
End LiftedEdges.

(* ================================================================= *)
(** * The diagram                                                     *)
(* ================================================================= *)

Section Diagram.
  Context {S A : Type} (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop).

  Local Notation R := (fun (us : unit * S) (r : A * S) => outSt m (snd us) (Some r)).

  (** ** WP implications *)

  Theorem TotalCorr_impl_PartCorr :
    TotalCorr b m c -> PartCorr b m c.
  Proof.
    exact (wpSt_under_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem LisbonLogic_impl_AngPartCorr :
    LisbonLogic b m c -> AngPartCorr b m c.
  Proof.
    exact (wpSt_under_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem TotalCorr_impl_LisbonLogic :
    TotalCorr b m c -> LisbonLogic b m c.
  Proof.
    exact (wpSt_under_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem PartCorr_impl_AngPartCorr :
    PartCorr b m c -> AngPartCorr b m c.
  Proof.
    exact (wpSt_under_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_over_impl_dwp_over :
    triple (@dwlpSt S) m Over b c -> triple (@dwpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_over_impl_awp_over :
    triple (@awlpSt S) m Over b c -> triple (@awpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem awp_over_impl_dwp_over :
    triple (@awpSt S) m Over b c -> triple (@dwpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem awlp_over_impl_dwlp_over :
    triple (@awlpSt S) m Over b c -> triple (@dwlpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  (** ** WP contrapositives *)

  Theorem LisbonLogic_contra_dwlp_over :
    LisbonLogic b m c
    <-> triple (@dwlpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@awpPure) (@dwlpPure)
             (fun X d => awpPure_contra_dwlpPure d) A m b c).
  Qed.

  Theorem AngPartCorr_contra_dwp_over :
    AngPartCorr b m c
    <-> triple (@dwpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@awlpPure) (@dwpPure)
             (fun X d => awlpPure_contra_dwpPure d) A m b c).
  Qed.

  Theorem TotalCorr_contra_awlp_over :
    TotalCorr b m c
    <-> triple (@awlpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@dwpPure) (@awlpPure)
             (fun X d => dwpPure_contra_awlpPure d) A m b c).
  Qed.

  Theorem PartCorr_contra_awp_over :
    PartCorr b m c
    <-> triple (@awpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@dwlpPure) (@awpPure)
             (fun X d => dwlpPure_contra_awpPure d) A m b c).
  Qed.

  (** ** SP implications *)

  Theorem aslp_over_impl_asp_over :
    triple (@aslpSt S) m Over b c -> triple (@aspSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_aspSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aslpSt m Over b c) H)).
  Qed.

  Theorem aslp_over_impl_dslp_over :
    triple (@aslpSt S) m Over b c -> triple (@dslpSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dslpSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_aslpSt m Over b c) H)).
  Qed.

  Theorem asp_over_impl_dsp_over :
    triple (@aspSt S) m Over b c -> triple (@dspSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_aspSt m Over b c) H)).
  Qed.

  Theorem dslp_over_impl_dsp_over :
    triple (@dslpSt S) m Over b c -> triple (@dspSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dslpSt m Over b c) H)).
  Qed.

  Theorem DemIncorr_impl_PartIncorr :
    DemIncorr b m c -> PartIncorr b m c.
  Proof.
    intro H. apply (proj2 (triple_dslpSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dspSt m Under b c) H)).
  Qed.

  Theorem DemIncorr_impl_IncorrLogic :
    DemIncorr b m c -> IncorrLogic b m c.
  Proof.
    intro H. apply (proj2 (triple_aspSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_dspSt m Under b c) H)).
  Qed.

  Theorem PartIncorr_impl_AngPartIncorr :
    PartIncorr b m c -> AngPartIncorr b m c.
  Proof.
    intro H. apply (proj2 (triple_aslpSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_dslpSt m Under b c) H)).
  Qed.

  Theorem IncorrLogic_impl_AngPartIncorr :
    IncorrLogic b m c -> AngPartIncorr b m c.
  Proof.
    intro H. apply (proj2 (triple_aslpSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aspSt m Under b c) H)).
  Qed.

  (** ** SP contrapositives *)

  Theorem DemIncorr_contra_aslp_over :
    DemIncorr b m c
    <-> triple (@aslpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dspSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aslpSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dsp_contra_aslp R)).
  Qed.

  Theorem PartIncorr_contra_asp_over :
    PartIncorr b m c
    <-> triple (@aspSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dslpSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aspSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dslp_contra_asp R)).
  Qed.

  Theorem IncorrLogic_contra_dslp_over :
    IncorrLogic b m c
    <-> triple (@dslpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aspSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dslpSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (asp_contra_dslp R)).
  Qed.

  Theorem AngPartIncorr_contra_dsp_over :
    AngPartIncorr b m c
    <-> triple (@dspSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aslpSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dspSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (aslp_contra_dsp R)).
  Qed.

  (** ** Galois connections *)

  Theorem PartCorr_galois_asp_over :
    PartCorr b m c <-> triple (@aspSt S) m Over b c.
  Proof.
    symmetry.
    refine (proj2 (galois_asp_rel (aspSt m)
                     (fun s Q => getWPure (runStateT (dwlpSt m) s) Q)) _ b c).
    intros s Q.
    etransitivity; [ exact (galois_slice_dwlpPure (runStateT m s) Q) |].
    split.
    - intros H y Hy. exact (H y (proj1 (aspRel_ofRel _ (tt, s) y) Hy)).
    - intros H a Ha. exact (H a (proj2 (aspRel_ofRel _ (tt, s) a) Ha)).
  Qed.

  Theorem awp_over_galois_PartIncorr :
    triple (@awpSt S) m Over b c <-> PartIncorr b m c.
  Proof.
    refine (proj2 (galois_dslp_rel
                     (fun s Q => getWPure (runStateT (awpSt m) s) Q)
                     (dslpSt m)) _ c b).
    intros s Q.
    etransitivity; [ exact (galois_awpPure_slice (runStateT m s) Q) |].
    split.
    - intros [a [Ha Hq]]. exists a.
      exact (conj (proj2 (dslpRel_ofRel _ (tt, s) a) Ha) Hq).
    - intros [y [Hy Hq]]. exists y.
      exact (conj (proj1 (dslpRel_ofRel _ (tt, s) y) Hy) Hq).
  Qed.
End Diagram.
