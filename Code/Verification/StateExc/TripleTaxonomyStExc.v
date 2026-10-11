(** * The taxonomy diagram, with state and exceptions

    The edges of [State/TripleTaxonomySt.v] for [m : stdivexcndNE S A], under
    the same names with [_exc]; the base lemmas are used at the result type
    [option (A * S)]. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Import SPostArr DSPASLPArr.
From Incorrectness.PTMonadTaxonomy Require Import TransformerRelations.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.PTMonadTaxonomy Require Import
  Carriers MonadTaxonomy.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Generic Require Import TripleTaxonomy.
From Incorrectness.Verification.Base Require Import DivNonDetNE.
From Incorrectness.Verification.Base Require Import MorphismsPure.
From Incorrectness.Verification.Base Require Import TriplesPure.
From Incorrectness.Verification.Base Require Import TripleTaxonomyPure.
From Incorrectness.Verification.StateExc Require Import ComputationStExc.
From Incorrectness.Verification.StateExc Require Import MorphismsStExc.
From Incorrectness.Verification.StateExc Require Import TriplesStExc.


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

  Theorem dwp_under_dwlp_under_exc :
    triple (@dwpStExc S) m Under b c -> triple (@dwlpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awp_under_awlp_under_exc :
    triple (@awpStExc S) m Under b c -> triple (@awlpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwp_under_awp_under_exc :
    triple (@dwpStExc S) m Under b c -> triple (@awpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem dwlp_under_awlp_under_exc :
    triple (@dwlpStExc S) m Under b c -> triple (@awlpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_over_dwp_over_exc :
    triple (@dwlpStExc S) m Over b c -> triple (@dwpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_over_awp_over_exc :
    triple (@awlpStExc S) m Over b c -> triple (@awpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem awp_over_dwp_over_exc :
    triple (@awpStExc S) m Over b c -> triple (@dwpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem awlp_over_dwlp_over_exc :
    triple (@awlpStExc S) m Over b c -> triple (@dwlpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  (** ** WP contrapositives *)

  Theorem awp_under_contra_dwlp_over_exc :
    triple (@awpStExc S) m Under b c
    <-> triple (@dwlpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@awpPure) (@dwlpPure)
             (fun X d => awpPure_contra_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_under_contra_dwp_over_exc :
    triple (@awlpStExc S) m Under b c
    <-> triple (@dwpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@awlpPure) (@dwpPure)
             (fun X d => awlpPure_contra_dwpPure d) A m b c).
  Qed.

  Theorem dwp_under_contra_awlp_over_exc :
    triple (@dwpStExc S) m Under b c
    <-> triple (@awlpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@dwpPure) (@awlpPure)
             (fun X d => dwpPure_contra_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_under_contra_awp_over_exc :
    triple (@dwlpStExc S) m Under b c
    <-> triple (@awpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@dwlpPure) (@awpPure)
             (fun X d => dwlpPure_contra_awpPure d) A m b c).
  Qed.

  (** ** SP implications *)

  Theorem aslp_over_asp_over_exc :
    triple (@aslpStExc S) m Over b c -> triple (@aspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_aspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aslpStExc m Over b c) H)).
  Qed.

  Theorem aslp_over_dslp_over_exc :
    triple (@aslpStExc S) m Over b c -> triple (@dslpStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dslpStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_aslpStExc m Over b c) H)).
  Qed.

  Theorem asp_over_dsp_over_exc :
    triple (@aspStExc S) m Over b c -> triple (@dspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_aspStExc m Over b c) H)).
  Qed.

  Theorem dslp_over_dsp_over_exc :
    triple (@dslpStExc S) m Over b c -> triple (@dspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dslpStExc m Over b c) H)).
  Qed.

  Theorem dsp_under_dslp_under_exc :
    triple (@dspStExc S) m Under b c -> triple (@dslpStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_dslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dspStExc m Under b c) H)).
  Qed.

  Theorem dsp_under_asp_under_exc :
    triple (@dspStExc S) m Under b c -> triple (@aspStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aspStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_dspStExc m Under b c) H)).
  Qed.

  Theorem dslp_under_aslp_under_exc :
    triple (@dslpStExc S) m Under b c -> triple (@aslpStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_dslpStExc m Under b c) H)).
  Qed.

  Theorem asp_under_aslp_under_exc :
    triple (@aspStExc S) m Under b c -> triple (@aslpStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aspStExc m Under b c) H)).
  Qed.

  (** ** SP contrapositives *)

  Theorem dsp_under_contra_aslp_over_exc :
    triple (@dspStExc S) m Under b c
    <-> triple (@aslpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dspStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aslpStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dsp_contra_aslp R)).
  Qed.

  Theorem dslp_under_contra_asp_over_exc :
    triple (@dslpStExc S) m Under b c
    <-> triple (@aspStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dslpStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aspStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dslp_contra_asp R)).
  Qed.

  Theorem asp_under_contra_dslp_over_exc :
    triple (@aspStExc S) m Under b c
    <-> triple (@dslpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aspStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dslpStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (asp_contra_dslp R)).
  Qed.

  Theorem aslp_under_contra_dsp_over_exc :
    triple (@aslpStExc S) m Under b c
    <-> triple (@dspStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aslpStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dspStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (aslp_contra_dsp R)).
  Qed.

  (** ** Galois connections *)

  Theorem dwlp_under_galois_asp_over_exc :
    triple (@dwlpStExc S) m Under b c <-> triple (@aspStExc S) m Over b c.
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

  Theorem awp_over_galois_dslp_under_exc :
    triple (@awpStExc S) m Over b c <-> triple (@dslpStExc S) m Under b c.
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
