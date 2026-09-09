From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import BaseGaloisConnections NewGaloisConnections.
Require Import Coq.Logic.Classical_Prop.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivNonDet_SPStExc.

Import MonadNotation.
Open Scope monad_scope.

(** * Taxonomy of the SP observations of [stdivnd] into [SPStExc]

    How the four observations of [SP/StDivNonDet_SPStExc.v] relate to one
    another — the contrapositive pairs, the conjunction/disjunction
    decompositions of [DSP]/[ASLP], and the orderings between them — and the
    taxonomy of the triples built on top. *)

Module TaxonomyFullOutcome.
Import FullOutcomeObs.

Section NDObservationComparisons.
  Variable S : Type.

  (* ================================================================== *)
  (** ** Contrapositive pairs                                           *)
  (* ================================================================== *)

  Theorem obsASP_contrapositive {A} (m : stdivnd S A) pre r :
    getASPStExc (obsASP m) pre r <-> ~ getDSLPStExc (obsDSLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [s [Hp Hr]] Hall. exact (Hall s Hr Hp).
    - intro Hnn. apply NNPP. intro Habs. apply Hnn.
      intros s Hr Hp. apply Habs. exists s. split; [ exact Hp | exact Hr ].
  Qed.

  Theorem obsDSLP_contrapositive {A} (m : stdivnd S A) pre r :
    getDSLPStExc (obsDSLP m) pre r <-> ~ getASPStExc (obsASP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros Hall [s [Hnp Hr]]. exact (Hnp (Hall s Hr)).
    - intros Hnn s Hr. apply NNPP. intro Hnp.
      exact (Hnn (ex_intro _ s (conj Hnp Hr))).
  Qed.
  
  Theorem obsDSP_contrapositive {A} (m : stdivnd S A) pre r :
    getDSPStExc (obsDSP m) pre r <-> ~ getASLPStExc (obsASLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] Hall] [[s' [Hnp Hr']] | Hall'].
      + exact (Hnp (Hall s' Hr')).
      + exact (Hall' s Hr Hp).
    - intro Hnn. split.
      + apply NNPP. intro Hnex. apply Hnn. right.
        intros s Hr Hp. apply Hnex. exists s. split; [ exact Hp | exact Hr ].
      + intros s Hr. apply NNPP. intro Hnp. apply Hnn. left.
        exists s. split; [ exact Hnp | exact Hr ].
  Qed.

  Theorem obsASLP_contrapositive {A} (m : stdivnd S A) pre r :
    getASLPStExc (obsASLP m) pre r <-> ~ getDSPStExc (obsDSP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] | Hall] [[s0 [Hnp0 Hr0]] Hall0].
      + exact (Hall0 s Hr Hp).
      + exact (Hnp0 (Hall s0 Hr0)).
    - intro Hnn.
      destruct (classic (exists s, pre s /\ unOptionT (runStateT m s) r))
        as [He | Hno]; [ left; exact He |].
      right. intros s Hr. apply NNPP. intro Hnp.
      apply Hnn. split.
      + exists s. split; [ exact Hnp | exact Hr ].
      + intros s0 Hr0 Hp0. exact (Hno (ex_intro _ s0 (conj Hp0 Hr0))).
  Qed.

  Theorem DSP_conjunction {A} (m : stdivnd S A) pre r :
    getDSPStExc (obsDSP m) pre r <-> (getASPStExc (obsASP m) pre r /\ getDSLPStExc (obsDSLP m) pre r).
  Proof. split; intro H; exact H. Qed.

  Theorem ASLP_disjunction {A} (m : stdivnd S A) pre r :
    getASLPStExc (obsASLP m) pre r <-> (getASPStExc (obsASP m) pre r \/ getDSLPStExc (obsDSLP m) pre r).
  Proof. split; intro H; exact H. Qed.

  Theorem ASP_ordering {A} (m : stdivnd S A) pre r :
    getASPStExc (obsASP m) pre r -> getASLPStExc (obsASLP m) pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem DSP_ordering {A} (m : stdivnd S A) pre r :
    getDSPStExc (obsDSP m) pre r -> getASPStExc (obsASP m) pre r.
  Proof. exact (@proj1 _ _). Qed.

  Theorem DSP_DSLP_ordering {A} (m : stdivnd S A) pre r :
    getDSPStExc (obsDSP m) pre r -> getDSLPStExc (obsDSLP m) pre r.
  Proof. exact (@proj2 _ _). Qed.

  Theorem DSLP_ordering {A} (m : stdivnd S A) pre r :
    getDSLPStExc (obsDSLP m) pre r -> getASLPStExc (obsASLP m) pre r.
  Proof. intro H. right. exact H. Qed.

    
End NDObservationComparisons.


(* ==================================================================== *)
(** * The taxonomy of triples                                            *)
(* ==================================================================== *)

Section NDTaxonomy.
  Variable S : Type.

  (** [Over]: the observation is a premise, so the WEAKEST transformer gives
      the STRONGEST triple — [ASLP => {ASP, DSLP} => DSP]. *)

  Theorem cc_aslp_implies_asp A (m : stdivnd S A) pre post :
    tripleASLP m Over pre post -> tripleASP m Over pre post.
  Proof. intros H r Hasp. apply (H r). left. exact Hasp. Qed.

  Theorem cc_aslp_implies_dslp A (m : stdivnd S A) pre post :
    tripleASLP m Over pre post -> tripleDSLP m Over pre post.
  Proof. intros H r Hdslp. apply (H r). right. exact Hdslp. Qed.

  Theorem cc_asp_implies_dsp A (m : stdivnd S A) pre post :
    tripleASP m Over pre post -> tripleDSP m Over pre post.
  Proof. intros H r [Hasp _]. exact (H r Hasp). Qed.

  Theorem cc_dslp_implies_dsp A (m : stdivnd S A) pre post :
    tripleDSLP m Over pre post -> tripleDSP m Over pre post.
  Proof. intros H r [_ Hdslp]. exact (H r Hdslp). Qed.

  (** [Under]: the observation is the conclusion, so everything flips. *)

  Theorem ii_dsp_implies_asp A (m : stdivnd S A) pre post :
    tripleDSP m Under pre post -> tripleASP m Under pre post.
  Proof. intros H r Hpost. exact (proj1 (H r Hpost)). Qed.

  Theorem ii_dsp_implies_dslp A (m : stdivnd S A) pre post :
    tripleDSP m Under pre post -> tripleDSLP m Under pre post.
  Proof. intros H r Hpost. exact (proj2 (H r Hpost)). Qed.

  Theorem ii_asp_implies_aslp A (m : stdivnd S A) pre post :
    tripleASP m Under pre post -> tripleASLP m Under pre post.
  Proof. intros H r Hpost. left. exact (H r Hpost). Qed.

  Theorem ii_dslp_implies_aslp A (m : stdivnd S A) pre post :
    tripleDSLP m Under pre post -> tripleASLP m Under pre post.
  Proof. intros H r Hpost. right. exact (H r Hpost). Qed.

  (** The two contrapositive diagonals. *)

  Theorem ci_asp_dslp_contrapositive A (m : stdivnd S A) pre post :
    tripleASP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSLP m Under pre post.
  Proof.
    intros Hii r Hpost s Hr. apply NNPP. intro Hnpre.
    apply (Hii r); [| exact Hpost ].
    exists s. split; [ exact Hnpre | exact Hr ].
  Qed.

  Theorem ci_dslp_asp_contrapositive A (m : stdivnd S A) pre post :
    tripleDSLP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASP m Under pre post.
  Proof.
    intros Hii r Hpost. apply NNPP. intro Hnex.
    apply (Hii r); [| exact Hpost ].
    intros s Hr Hpre. apply Hnex. exists s. split; [ exact Hpre | exact Hr ].
  Qed.

  Theorem ci_aslp_dsp_contrapositive A (m : stdivnd S A) pre post :
    tripleASLP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSP m Under pre post.
  Proof.
    intros H r Hpost. split.
    - apply NNPP. intro Hnex. apply (H r); [| exact Hpost ]. right.
      intros s Hr Hp. apply Hnex. exists s. split; [ exact Hp | exact Hr ].
    - intros s Hr. apply NNPP. intro Hnp. apply (H r); [| exact Hpost ]. left.
      exists s. split; [ exact Hnp | exact Hr ].
  Qed.

  Theorem ci_aslp_dsp_contrapositive' A (m : stdivnd S A) pre post :
    tripleDSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASLP m Over pre post.
  Proof.
    intros H r Haslp. apply NNPP. intro Hnpost.
    destruct (H r Hnpost) as [[s0 [Hnp Hr0]] Hall].
    destruct Haslp as [[s [Hp Hr]] | Hall2].
    - exact (Hall s Hr Hp).
    - exact (Hnp (Hall2 s0 Hr0)).
  Qed.

  Theorem ci_dsp_aslp_contrapositive A (m : stdivnd S A) pre post :
    tripleDSP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASLP m Under pre post.
  Proof.
    intros H r Hpost. apply NNPP. intro Hno.
    apply (H r); [| exact Hpost ]. split.
    - (* [~ asp pre] is [dslp (~pre)] ... *)
      apply NNPP. intro Hnex. apply Hno. right.
      intros s Hr. apply NNPP. intro Hnp.
      exact (Hnex (ex_intro _ s (conj Hnp Hr))).
    - (* ... and [~ dslp pre] is [asp (~pre)] *)
      intros s Hr. apply NNPP. intro Hnnp. apply Hno. left.
      exists s. split; [ apply NNPP; exact Hnnp | exact Hr ].
  Qed.

  Theorem ci_dslp_asp_contrapositive' A (m : stdivnd S A) pre post :
    tripleASP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSLP m Over pre post.
  Proof.
    intros H r Hdslp. apply NNPP. intro Hnpost.
    destruct (H r Hnpost) as [s [Hnp Hr]].
    exact (Hnp (Hdslp s Hr)).
  Qed.

End NDTaxonomy.

End TaxonomyFullOutcome.
